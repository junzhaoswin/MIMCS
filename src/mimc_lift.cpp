// ============================================================================
// mimc_lift.cpp  —  Gadget-Closure Lift for MIMC (practical E2-style pipeline)
// ----------------------------------------------------------------------------
// Implements, per the note "Gadget-Closure Lifting for MIMC":
//   1. Relational core peeling (unique max constraint-satisfying set; comps =
//      maximal connected r-coms).                                   [Fact 1.1]
//   2. Protected-peel anchored gadget finder K_v with certificates
//      gamma(v)=c(K_v); family parameters (sigma_c, theta) are REPORTED from
//      the found family, never assumed.                             [Def 2.1]
//   3. Closure-greedy lift solver (E2 budget semantics: the union closure is
//      metered by ACTUAL incremental cost, which dominates the gamma-metering
//      of Thm E2, so feasibility at the true budget b is maintained by
//      construction). Fallbacks: best gadget, best feasible singleton.
//   4. Flattened influence model: Gamma_T entry map (identity / typed
//      meta-paths), target graph G_T (direct / length-2 projection / file),
//      IC (WC or const-p), RR-set oracle Score, forward-MC cross-check.
//   5. Root upper bounds on Score (live-set / component-reach / fractional
//      knapsack; min taken) — all proved valid upper bounds.
//   6. Two-collection a-posteriori certificate  c_hat  (Prop. cert):
//      sigma(S_hat) >= c_hat * OPT_sigma  w.p. >= 1-delta,
//      c_hat = (Score_R2(S_hat) - lam2)^+ / (UB_R1 + lam1).
//   7. --mode selftest : randomized differential harness (brute force over all
//      feasible communities on small instances) checking:
//        (C1) core == brute-force maximum satisfying set (n<=16)
//        (C2) every gadget passes an independent r-com verifier
//        (C3) UB_R1 >= exact OPT of Score on R1 (brute force)
//        (C4) solver output passes the independent verifier (budget incl.)
//        (C5) solver Score <= exact OPT (sanity)
//        (C6) RR estimate of sigma(S_hat) consistent with forward MC (4-sigma)
//        (C7) certificate internal consistency (c_hat*(UB+lam1) <= Score_R2)
//        (C8) exact B&B (no warm start) == brute-force OPT (both complete)
//        (C9) exact B&B output passes the independent verifier
//   8. --mode exact : scalable exact solver (branch-and-bound over connected
//      sets with incremental protected-peel pruning and fractional-knapsack
//      bounds; anytime — the time limit yields a certified upper bound).
//   9. --algo <variant> : the two public exact-solver variants
//      advanced_full (MIMC-B&B) and baseline_enum (MIMC-Enum).
//
// Build:   g++ -O2 -std=c++17 -Wall -Wextra -o mimc_lift mimc_lift.cpp
// Public modes:
//          ./mimc_lift --mode config --graph g.txt --config c.txt
//          ./mimc_lift --mode query_exact --graph g --config c --query v
//                      --algo advanced_full|baseline_enum
//                      [--budget B --timelimit S --seed S]
//          ./mimc_lift --mode selftest --algo <variant>   (per-variant C8/C10/C11)
//
// solve-mode file formats -----------------------------------------------------
// graph file:
//     n m ntypes
//     <type_i> <cost_i>          (n lines, vertex ids 0..n-1)
//     <u> <v>                    (m lines, undirected; dups/self-loops ignored)
// config file (key=value or key value, '#' comments):
//     constraint A1 A2 k         (repeatable)
//     AS 0,1,2                   (optional; default = types in constraints)
//     target_type t
//     gamma_mode identity|metapath
//     gamma_path 2,1,0           (type sequence ending at target; repeatable)
//     gt_mode direct|proj2|file
//     gt_middle m                (for proj2: target-middle-target)
//     gt_file path               (edge list "u v" over target vertices)
//     ic_model wc|const          ic_p 0.05
//     budget B    rr1 200000  rr2 200000  delta 0.1
//     ball_hops 2  ball_cap 400  minimize_passes 3
// ----------------------------------------------------------------------------
// Honest scoping (matches the note):
//  * The greedy tree-builder is a HEURISTIC stand-in for the E1/E2 boxes; the
//    operative guarantee is the reported certificate c_hat, not a worst-case
//    ratio. CELF-style laziness is not exact for gain/cost ratios (both
//    numerator and incremental cost shrink as U grows), so the solver
//    re-evaluates the top of the queue until stable — documented heuristic.
//  * proj2 target-graph materialization can blow up on hub-heavy HINs; it is
//    capped and warns. For real datasets choose the projection deliberately.
// ============================================================================

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace std;
typedef long long ll;
typedef unsigned long long ull;

// ---------------------------------------------------------------- utilities
struct Stamp {                    // epoch-stamped scratch marks (no clearing)
    vector<int> m; int cur = 0;
    void init(size_t n) { m.assign(n, 0); cur = 0; }
    void fresh() { ++cur; if (cur == INT32_MAX) { fill(m.begin(), m.end(), 0); cur = 1; } }
    bool test(int i) const { return m[i] == cur; }
    void set(int i) { m[i] = cur; }
};
static inline void sort_uniq(vector<int>& v) {
    sort(v.begin(), v.end()); v.erase(unique(v.begin(), v.end()), v.end());
}

// -------------------------------------------------------------------- graph
struct HIN {
    int n = 0, ntypes = 0;
    vector<int> type;
    vector<double> cost;
    vector<int> off, adj;         // CSR, undirected, deduped
    void build(int n_, int ntypes_, vector<int> ty, vector<double> co,
               vector<pair<int,int>>& edges) {
        n = n_; ntypes = ntypes_; type = std::move(ty); cost = std::move(co);
        vector<pair<int,int>> es;
        es.reserve(edges.size() * 2);
        for (auto& e : edges) {
            if (e.first == e.second) continue;
            es.push_back(e); es.push_back({e.second, e.first});
        }
        sort(es.begin(), es.end());
        es.erase(unique(es.begin(), es.end()), es.end());
        off.assign(n + 1, 0);
        for (auto& e : es) off[e.first + 1]++;
        for (int i = 0; i < n; i++) off[i + 1] += off[i];
        adj.resize(es.size());
        {
            vector<int> pos(off.begin(), off.end() - 1);
            for (auto& e : es) adj[pos[e.first]++] = e.second;
        }
    }
    inline int deg(int v) const { return off[v + 1] - off[v]; }
};

// ------------------------------------------------------------------- config
struct Constraint { int A1, A2, k; };
struct Cfg {
    vector<Constraint> cons;
    vector<int> AS;                       // involved types
    bool AS_explicit = false;
    int target_type = 0;
    string gamma_mode = "identity";       // identity | metapath
    vector<vector<int>> gamma_paths;      // type sequences ending at target
    string gt_mode = "direct";            // direct | proj2 | file
    int gt_middle = 1;
    string gt_file = "";
    string ic_model = "wc";               // wc | const
    double ic_p = 0.05;
    double budget = 10;
    ll rr1 = 100000, rr2 = 100000;
    double delta = 0.1;
    int ball_hops = 2, ball_cap = 400, minimize_passes = 3;
    ll proj_edge_cap = 30'000'000;
    // derived
    vector<char> inAS, hasCons;                     // per type
    vector<vector<pair<int,int>>> consOf;           // type -> (A2,k)
    bool finalize(int ntypes, string* err = nullptr) {
        auto fail = [&](const string& msg) {
            if (err) *err = msg;
            return false;
        };
        if (err) err->clear();

        map<pair<int,int>, int> best;
        for (auto& c : cons) {
            if (c.A1 < 0 || c.A1 >= ntypes || c.A2 < 0 || c.A2 >= ntypes)
                return fail("constraint type out of range: " + to_string(c.A1) +
                            " -> " + to_string(c.A2) + " with ntypes=" + to_string(ntypes));
            if (c.k < 0)
                return fail("constraint degree must be non-negative for " +
                            to_string(c.A1) + " -> " + to_string(c.A2));
            auto key = make_pair(c.A1, c.A2);
            auto it = best.find(key);
            if (it == best.end() || c.k > it->second) best[key] = c.k;
        }
        vector<pair<int,int>> orderedPairs;
        for (auto& kv : best) orderedPairs.push_back(kv.first);
        for (auto& p : orderedPairs) {
            if (p.first == p.second) continue;
            auto rev = make_pair(p.second, p.first);
            if (!best.count(rev)) best[rev] = 1;
        }
        cons.clear();
        for (auto& kv : best)
            cons.push_back({kv.first.first, kv.first.second, kv.second});

        vector<char> mentioned(ntypes, 0);
        for (auto& c : cons) { mentioned[c.A1] = 1; mentioned[c.A2] = 1; }
        if (AS_explicit) {
            for (int t : AS)
                if (t < 0 || t >= ntypes)
                    return fail("AS type out of range: " + to_string(t) +
                                " with ntypes=" + to_string(ntypes));
            sort_uniq(AS);
        } else {
            AS.clear();
            for (int t = 0; t < ntypes; t++) if (mentioned[t]) AS.push_back(t);
            if (AS.empty()) for (int t = 0; t < ntypes; t++) AS.push_back(t);
        }
        consOf.assign(ntypes, {});
        for (auto& c : cons) consOf[c.A1].push_back({c.A2, c.k});
        inAS.assign(ntypes, 0); hasCons.assign(ntypes, 0);
        for (int t : AS) inAS[t] = 1;
        if (AS_explicit) {
            for (auto& c : cons) {
                if (!inAS[c.A1])
                    return fail("explicit AS is missing type " + to_string(c.A1) +
                                " appearing in effective constraint " +
                                to_string(c.A1) + " -> " + to_string(c.A2));
                if (!inAS[c.A2])
                    return fail("explicit AS is missing type " + to_string(c.A2) +
                                " appearing in effective constraint " +
                                to_string(c.A1) + " -> " + to_string(c.A2));
            }
            if (!cons.empty()) for (int t : AS) if (!mentioned[t])
                return fail("explicit AS contains unconstrained type " + to_string(t) +
                            "; remove it from AS or add a constraint involving it");
        }
        for (auto& c : cons) hasCons[c.A1] = 1;
        return true;
    }
    void print_effective(FILE* out) const {
        fprintf(out, "config: AS:");
        for (int t : AS) fprintf(out, " %d", t);
        fprintf(out, "\n");
        fprintf(out, "config: constraints:\n");
        for (auto& c : cons)
            fprintf(out, "  %d -> %d : %d\n", c.A1, c.A2, c.k);
    }
};

// ----------------------------------------------------- relational core peel
// Peels within 'member' (member[v]!=0 means candidate) to the unique maximum
// constraint-satisfying subset; result in alive[]. Types outside AS are dead.
static void peel_core(const HIN& G, const Cfg& C, const vector<char>& member,
                      vector<char>& alive) {
    int n = G.n;
    alive.assign(n, 0);
    vector<int> vcOff(n + 1, 0);
    for (int v = 0; v < n; v++)
        vcOff[v + 1] = vcOff[v] + (int)C.consOf[G.type[v]].size();
    vector<int> cnt(vcOff[n], 0);
    for (int v = 0; v < n; v++)
        alive[v] = member[v] && C.inAS[G.type[v]];
    for (int v = 0; v < n; v++) if (alive[v]) {
        auto& cs = C.consOf[G.type[v]];
        for (int e = G.off[v]; e < G.off[v + 1]; e++) {
            int u = G.adj[e]; if (!alive[u]) continue;
            for (size_t i = 0; i < cs.size(); i++)
                if (cs[i].first == G.type[u]) cnt[vcOff[v] + (int)i]++;
        }
    }
    auto violates = [&](int v) {
        auto& cs = C.consOf[G.type[v]];
        for (size_t i = 0; i < cs.size(); i++)
            if (cnt[vcOff[v] + (int)i] < cs[i].second) return true;
        return false;
    };
    queue<int> q;
    for (int v = 0; v < n; v++) if (alive[v] && violates(v)) q.push(v);
    while (!q.empty()) {
        int v = q.front(); q.pop();
        if (!alive[v] || !violates(v)) continue;
        alive[v] = 0;
        for (int e = G.off[v]; e < G.off[v + 1]; e++) {
            int u = G.adj[e]; if (!alive[u]) continue;
            auto& cs = C.consOf[G.type[u]];
            bool hit = false;
            for (size_t i = 0; i < cs.size(); i++)
                if (cs[i].first == G.type[v]) { cnt[vcOff[u] + (int)i]--; hit = true; }
            if (hit && violates(u)) q.push(u);
        }
    }
}

static void components_of(const HIN& G, const vector<char>& alive,
                          vector<int>& comp, vector<vector<int>>& comps) {
    comp.assign(G.n, -1); comps.clear();
    for (int s = 0; s < G.n; s++) if (alive[s] && comp[s] < 0) {
        int id = (int)comps.size(); comps.push_back({});
        queue<int> q; q.push(s); comp[s] = id;
        while (!q.empty()) {
            int v = q.front(); q.pop(); comps[id].push_back(v);
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e];
                if (alive[u] && comp[u] < 0) { comp[u] = id; q.push(u); }
            }
        }
    }
}

// ------------------------------------------------------ independent verifier
// No shared state with the solver: recomputes everything from scratch.
static bool verify_community(const HIN& G, const Cfg& C, const vector<int>& S,
                             double budget, string& why) {
    if (S.empty()) { why = "empty"; return false; }
    vector<int> s = S; sort_uniq(s);
    if (s.size() != S.size()) { why = "duplicate vertices"; return false; }
    double c = 0; for (int v : s) c += G.cost[v];
    if (c > budget + 1e-9 + 1e-12 * fabs(budget)) { why = "over budget"; return false; }
    vector<char> in(G.n, 0); for (int v : s) in[v] = 1;
    for (int v : s) {
        if (!C.inAS[G.type[v]]) { why = "type outside AS"; return false; }
        for (auto& pr : C.consOf[G.type[v]]) {
            int need = pr.second, have = 0;
            for (int e = G.off[v]; e < G.off[v + 1]; e++)
                if (in[G.adj[e]] && G.type[G.adj[e]] == pr.first) have++;
            if (have < need) { why = "typed-degree violated"; return false; }
        }
    }
    // connectivity
    queue<int> q; q.push(s[0]);
    vector<char> vis(G.n, 0); vis[s[0]] = 1; size_t cnt = 1;
    while (!q.empty()) {
        int v = q.front(); q.pop();
        for (int e = G.off[v]; e < G.off[v + 1]; e++) {
            int u = G.adj[e];
            if (in[u] && !vis[u]) { vis[u] = 1; cnt++; q.push(u); }
        }
    }
    if (cnt != s.size()) { why = "disconnected"; return false; }
    why = "ok"; return true;
}

// --------------------------------------------------------- influence oracle
struct Influence {
    // target graph
    int nT = 0;
    vector<int> tid;                 // vertex -> target index (or -1)
    vector<int> targets;             // target index -> vertex
    vector<int> gOff, gAdj;          // CSR over target indices
    vector<double> gW, gWtot;        // per-edge weight (meta-path multiplicity)
    // entry map Gamma_T : vertex -> sorted target indices
    vector<vector<int>> gamma;
    // RR collections
    struct RRcol {
        ll R = 0;
        vector<vector<int>> perTarget;    // target index -> RR ids containing it
    };
    RRcol col1, col2;
    vector<vector<int>> cov1, cov2;       // vertex -> sorted RR ids (per col)
    mutable Stamp rrStamp1, rrStamp2, tStamp;

    void build_targets(const HIN& G, const Cfg& C) {
        tid.assign(G.n, -1);
        for (int v = 0; v < G.n; v++)
            if (G.type[v] == C.target_type) { tid[v] = nT++; targets.push_back(v); }
    }
    void build_gt(const HIN& G, const Cfg& C) {
        vector<pair<int,int>> es;
        if (C.gt_mode == "direct") {
            for (int v = 0; v < G.n; v++) if (tid[v] >= 0)
                for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                    int u = G.adj[e];
                    if (tid[u] >= 0 && tid[v] < tid[u]) es.push_back({tid[v], tid[u]});
                }
        } else if (C.gt_mode == "proj2") {
            ll produced = 0;
            for (int m = 0; m < G.n; m++) if (G.type[m] == C.gt_middle) {
                vector<int> ts;
                for (int e = G.off[m]; e < G.off[m + 1]; e++)
                    if (tid[G.adj[e]] >= 0) ts.push_back(tid[G.adj[e]]);
                sort_uniq(ts);
                produced += (ll)ts.size() * (ll)max<size_t>(ts.size(), 1);
                if (produced > C.proj_edge_cap) {
                    fprintf(stderr, "[warn] proj2 edge cap hit; projection truncated\n");
                    break;
                }
                for (size_t i = 0; i < ts.size(); i++)
                    for (size_t j = i + 1; j < ts.size(); j++)
                        es.push_back({ts[i], ts[j]});
            }
        } else if (C.gt_mode == "file") {
            ifstream f(C.gt_file);
            int a, b;
            while (f >> a >> b)
                if (tid[a] >= 0 && tid[b] >= 0 && tid[a] != tid[b])
                    es.push_back({min(tid[a], tid[b]), max(tid[a], tid[b])});
        }
        // CSR over target indices (undirected); duplicate pairs (one per
        // meta-path instance, e.g. one per co-authored paper) become edge
        // weights — the real per-edge propagation strength
        vector<pair<int,int>> ds; ds.reserve(es.size() * 2);
        for (auto& e : es) { ds.push_back(e); ds.push_back({e.second, e.first}); }
        sort(ds.begin(), ds.end());
        gOff.assign(nT + 1, 0);
        vector<pair<int,int>> uq; vector<double> wq;
        for (size_t i = 0; i < ds.size(); ) {
            size_t j = i;
            while (j < ds.size() && ds[j] == ds[i]) j++;
            uq.push_back(ds[i]); wq.push_back((double)(j - i));
            i = j;
        }
        for (auto& e : uq) gOff[e.first + 1]++;
        for (int i = 0; i < nT; i++) gOff[i + 1] += gOff[i];
        gAdj.resize(uq.size()); gW.resize(uq.size());
        gWtot.assign(nT, 0.0);
        vector<int> pos(gOff.begin(), gOff.end() - 1);
        for (size_t k = 0; k < uq.size(); k++) {
            gAdj[pos[uq[k].first]] = uq[k].second;
            gW[pos[uq[k].first]] = wq[k];
            gWtot[uq[k].first] += wq[k];
            pos[uq[k].first]++;
        }
    }
    inline int gdeg(int t) const { return gOff[t + 1] - gOff[t]; }
    void build_gamma(const HIN& G, const Cfg& C) {
        gamma.assign(G.n, {});
        for (int v = 0; v < G.n; v++) if (tid[v] >= 0) gamma[v].push_back(tid[v]);
        if (C.gamma_mode == "metapath") {
            for (auto& path : C.gamma_paths) {
                if (path.empty() || path.back() != C.target_type) continue;
                for (int v = 0; v < G.n; v++) {
                    if (G.type[v] != path[0]) continue;
                    vector<int> frontier = {v};
                    for (size_t step = 1; step < path.size(); step++) {
                        vector<int> nxt;
                        for (int x : frontier)
                            for (int e = G.off[x]; e < G.off[x + 1]; e++)
                                if (G.type[G.adj[e]] == path[step]) nxt.push_back(G.adj[e]);
                        sort_uniq(nxt);
                        if (nxt.size() > 5000) nxt.resize(5000);  // fan-out cap (warned in docs)
                        frontier = std::move(nxt);
                        if (frontier.empty()) break;
                    }
                    for (int t : frontier) gamma[v].push_back(tid[t]);
                }
            }
            for (int v = 0; v < G.n; v++) sort_uniq(gamma[v]);
        }
    }
    // one RR set: reverse reachable from a uniform target root under IC
    void sample_rr(const Cfg& C, mt19937_64& rng, vector<int>& out) const {
        out.clear();
        if (nT == 0) return;
        uniform_real_distribution<double> U(0.0, 1.0);
        int root = (int)(rng() % (ull)nT);
        tStamp.fresh();
        vector<int> q = {root}; tStamp.set(root); out.push_back(root);
        bool wic = (C.ic_model == "wic");
        for (size_t h = 0; h < q.size(); h++) {
            int x = q[h];
            double px = (C.ic_model == "wc") ? (gdeg(x) ? 1.0 / gdeg(x) : 0.0) : C.ic_p;
            for (int e = gOff[x]; e < gOff[x + 1]; e++) {
                int u = gAdj[e];
                double p = wic ? (gWtot[x] > 0 ? gW[e] / gWtot[x] : 0.0) : px;
                if (!tStamp.test(u) && U(rng) < p) {
                    tStamp.set(u); q.push_back(u); out.push_back(u);
                }
            }
        }
    }
    void build_collection(const HIN& G, const Cfg& C, mt19937_64& rng, ll R,
                          RRcol& col, vector<vector<int>>& cov) {
        col.R = R; col.perTarget.assign(nT, {});
        vector<int> rr;
        for (ll j = 0; j < R; j++) {
            sample_rr(C, rng, rr);
            for (int t : rr) col.perTarget[t].push_back((int)j);
        }
        cov.assign(G.n, {});
        for (int v = 0; v < G.n; v++) {
            for (int t : gamma[v])
                cov[v].insert(cov[v].end(), col.perTarget[t].begin(), col.perTarget[t].end());
            sort_uniq(cov[v]);
        }
    }
    void init(const HIN& G, const Cfg& C, mt19937_64& rng) {
        build_targets(G, C); build_gt(G, C); build_gamma(G, C);
        tStamp.init(max(nT, 1));
        build_collection(G, C, rng, C.rr1, col1, cov1);
        build_collection(G, C, rng, C.rr2, col2, cov2);
        rrStamp1.init((size_t)max<ll>(C.rr1, 1));
        rrStamp2.init((size_t)max<ll>(C.rr2, 1));
    }
    // raw covered counts (scale by nT/R for Score units)
    ll covered(const vector<int>& S, int which) const {
        const auto& cov = (which == 1) ? cov1 : cov2;
        Stamp& st = (which == 1) ? rrStamp1 : rrStamp2;
        st.fresh(); ll c = 0;
        for (int v : S) for (int j : cov[v]) if (!st.test(j)) { st.set(j); c++; }
        return c;
    }
    double score(const vector<int>& S, int which) const {
        ll R = (which == 1) ? col1.R : col2.R;
        if (R == 0 || nT == 0) return 0.0;
        return (double)nT * (double)covered(S, which) / (double)R;
    }
    // forward MC estimate of sigma(S) under the same IC model
    double forward_mc(const HIN& /*G*/, const Cfg& C, const vector<int>& S,
                      int sims, mt19937_64& rng, double& se) const {
        uniform_real_distribution<double> U(0.0, 1.0);
        vector<int> seeds; for (int v : S) for (int t : gamma[v]) seeds.push_back(t);
        sort_uniq(seeds);
        double sum = 0, sq = 0;
        vector<int> q;
        for (int s = 0; s < sims; s++) {
            tStamp.fresh(); q.clear();
            for (int t : seeds) { tStamp.set(t); q.push_back(t); }
            for (size_t h = 0; h < q.size(); h++) {
                int x = q[h];
                for (int e = gOff[x]; e < gOff[x + 1]; e++) {
                    int u = gAdj[e];
                    if (tStamp.test(u)) continue;
                    double p = (C.ic_model == "wic")
                        ? (gWtot[u] > 0 ? gW[e] / gWtot[u] : 0.0)
                        : (C.ic_model == "wc") ? (gdeg(u) ? 1.0 / gdeg(u) : 0.0)
                                               : C.ic_p;
                    if (U(rng) < p) { tStamp.set(u); q.push_back(u); }
                }
            }
            double a = (double)q.size();
            sum += a; sq += a * a;
        }
        double mean = sum / sims;
        double var = max(0.0, sq / sims - mean * mean);
        se = sqrt(var / sims);
        return mean;
    }
};

// ------------------------------------------------------------ gadget finder
struct GadgetFinder {
    const HIN& G; const Cfg& C; const vector<char>& coreAlive;
    const Influence& inf;
    vector<vector<int>> K;       // per-vertex gadget (empty if none/uncomputed)
    vector<char> computed, ok;
    GadgetFinder(const HIN& g, const Cfg& c, const vector<char>& a, const Influence& I)
        : G(g), C(c), coreAlive(a), inf(I) {
        K.assign(G.n, {}); computed.assign(G.n, 0); ok.assign(G.n, 0);
    }
    static double cost_of(const HIN& G, const vector<int>& S) {
        double c = 0; for (int v : S) c += G.cost[v]; return c;
    }
    // cascade within 'mem' after removing 'kill' (or -1); returns component of
    // anchor if anchor survives, else empty. Local (small-ball) implementation.
    bool cascade_component(const vector<int>& mem, int anchor, int kill,
                           vector<int>& out) const {
        vector<int> loc(mem);                     // local id -> vertex
        int m = (int)loc.size();
        // vertex -> local id via temp map
        static thread_local vector<int> gid; static thread_local vector<int> touched;
        if ((int)gid.size() < G.n) gid.assign(G.n, -1);
        touched.clear();
        for (int i = 0; i < m; i++) { gid[loc[i]] = i; touched.push_back(loc[i]); }
        vector<char> alive(m, 1);
        if (kill >= 0 && gid[kill] >= 0) alive[gid[kill]] = 0;
        // typed counters
        vector<vector<int>> cnt(m);
        for (int i = 0; i < m; i++) {
            int v = loc[i];
            auto& cs = C.consOf[G.type[v]];
            cnt[i].assign(cs.size(), 0);
            if (!alive[i]) continue;
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e]; int j = gid[u];
                if (j < 0 || !alive[j]) continue;
                for (size_t x = 0; x < cs.size(); x++)
                    if (cs[x].first == G.type[u]) cnt[i][x]++;
            }
        }
        auto viol = [&](int i) {
            auto& cs = C.consOf[G.type[loc[i]]];
            for (size_t x = 0; x < cs.size(); x++)
                if (cnt[i][x] < cs[x].second) return true;
            return false;
        };
        queue<int> q;
        for (int i = 0; i < m; i++) if (alive[i] && viol(i)) q.push(i);
        while (!q.empty()) {
            int i = q.front(); q.pop();
            if (!alive[i] || !viol(i)) continue;
            alive[i] = 0;
            int v = loc[i];
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e]; int j = gid[u];
                if (j < 0 || !alive[j]) continue;
                auto& cs = C.consOf[G.type[u]];
                bool hit = false;
                for (size_t x = 0; x < cs.size(); x++)
                    if (cs[x].first == G.type[v]) { cnt[j][x]--; hit = true; }
                if (hit && viol(j)) q.push(j);
            }
        }
        out.clear();
        int ai = gid[anchor];
        bool good = (ai >= 0 && alive[ai]);
        if (good) {                                // BFS component of anchor
            vector<char> vis(m, 0); vector<int> bq = {ai}; vis[ai] = 1;
            for (size_t h = 0; h < bq.size(); h++) {
                int i = bq[h]; out.push_back(loc[i]);
                int v = loc[i];
                for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                    int j = gid[G.adj[e]];
                    if (j >= 0 && alive[j] && !vis[j]) { vis[j] = 1; bq.push_back(j); }
                }
            }
            sort(out.begin(), out.end());
        }
        for (int v : touched) gid[v] = -1;
        return good;
    }
    void compute(int v0) {
        if (computed[v0]) return;
        computed[v0] = 1; ok[v0] = 0;
        if (!coreAlive[v0]) return;
        int hops = C.ball_hops;
        vector<int> ball;
        for (int attempt = 0; attempt < 4; attempt++, hops *= 2) {
            // BFS ball within core
            ball.clear();
            static thread_local Stamp st; if ((int)st.m.size() < G.n) st.init(G.n);
            st.fresh();
            vector<pair<int,int>> q = {{v0, 0}}; st.set(v0); ball.push_back(v0);
            for (size_t h = 0; h < q.size(); h++) {
                auto [x, d] = q[h];
                if (d >= hops || (int)ball.size() >= C.ball_cap) continue;
                for (int e = G.off[x]; e < G.off[x + 1]; e++) {
                    int u = G.adj[e];
                    if (coreAlive[u] && !st.test(u)) {
                        st.set(u); ball.push_back(u); q.push_back({u, d + 1});
                        if ((int)ball.size() >= C.ball_cap) break;
                    }
                }
            }
            sort(ball.begin(), ball.end());
            vector<int> comp;
            if (!cascade_component(ball, v0, -1, comp)) continue;   // grow ball
            // greedy minimization by (cost desc)
            for (int pass = 0; pass < C.minimize_passes; pass++) {
                vector<int> order = comp;
                sort(order.begin(), order.end(), [&](int a, int b) {
                    if (G.cost[a] != G.cost[b]) return G.cost[a] > G.cost[b];
                    return inf.cov1[a].size() < inf.cov1[b].size();
                });
                bool changed = false;
                for (int w : order) {
                    if (w == v0) continue;
                    if (!binary_search(comp.begin(), comp.end(), w)) continue;
                    vector<int> nc;
                    if (cascade_component(comp, v0, w, nc) &&
                        cost_of(G, nc) < cost_of(G, comp) - 1e-12) {
                        comp = std::move(nc); changed = true;
                    }
                }
                if (!changed) break;
            }
            K[v0] = comp; ok[v0] = 1; return;
        }
        // last resort: whole component would be the gadget; leave uncomputed-fail
    }
    double gammaCost(int v) { compute(v); return ok[v] ? cost_of(G, K[v]) : 1e300; }
};

// ------------------------------------------------------------ upper bounds
// All in raw covered-count units on collection 1; min of valid bounds.
static ll ub_component(const Influence& inf, const vector<int>& compVerts) {
    return inf.covered(compVerts, 1);                       // UB_reach at root
}
static ll ub_frac_knapsack(const HIN& G, const Influence& inf,
                           const vector<int>& compVerts, double b) {
    // OPT_cover <= fractional knapsack over singleton covers (subadditivity)
    vector<pair<double,int>> items;                          // (density, v)
    for (int v : compVerts) {
        ll cv = (ll)inf.cov1[v].size();
        if (cv > 0) items.push_back({(double)cv / G.cost[v], v});
    }
    sort(items.begin(), items.end(), greater<>());
    double rem = b, val = 0;
    for (auto& it : items) {
        double c = G.cost[it.second], cv = (double)inf.cov1[it.second].size();
        if (c <= rem) { rem -= c; val += cv; }
        else { val += cv * (rem / c); break; }
    }
    return (ll)ceil(val - 1e-9);
}
// Conditioned-marginal bound: for ANY set S,
//   cov(O) <= cov(S) + sum_{v in O} Delta(v|S) <= cov(S) + fracknap_b(Delta(.|S))
// (submodularity + c(O)<=b). S is chosen by an unconstrained lazy density
// greedy — the CHOICE of S affects only tightness, never validity, so lazy
// staleness is harmless here.
static ll ub_marg_conditioned(const HIN& G, const Influence& inf,
                              const vector<int>& compVerts, double b) {
    static Stamp cover; 
    if (cover.m.size() < (size_t)max<ll>(inf.col1.R, 1))
        cover.init((size_t)max<ll>(inf.col1.R, 1));
    cover.fresh();
    auto freshGain = [&](int v) {
        ll g = 0;
        for (int j : inf.cov1[v]) if (!cover.test(j)) g++;
        return g;
    };
    priority_queue<pair<double,int>> pq;                      // (stale ratio, v)
    for (int v : compVerts)
        if (!inf.cov1[v].empty())
            pq.push({(double)inf.cov1[v].size() / G.cost[v], v});
    double rem = b; ll covS = 0; int pops = 0;
    while (!pq.empty() && pops++ < 200000) {
        auto [r, v] = pq.top(); pq.pop();
        if (G.cost[v] > rem + 1e-12) continue;                // can never fit
        ll g = freshGain(v);
        if (g <= 0) continue;
        double fr = (double)g / G.cost[v];
        if (!pq.empty() && fr + 1e-12 < pq.top().first) { pq.push({fr, v}); continue; }
        rem -= G.cost[v]; covS += g;
        for (int j : inf.cov1[v]) if (!cover.test(j)) cover.set(j);
    }
    // fractional knapsack of conditioned marginals into the FULL budget b
    vector<pair<double,int>> items;
    vector<ll> gain(compVerts.size());
    for (size_t i = 0; i < compVerts.size(); i++) {
        gain[i] = freshGain(compVerts[i]);
        if (gain[i] > 0)
            items.push_back({(double)gain[i] / G.cost[compVerts[i]], (int)i});
    }
    sort(items.begin(), items.end(), greater<>());
    double rem2 = b, val = (double)covS;
    for (auto& it : items) {
        double c = G.cost[compVerts[it.second]], gv = (double)gain[it.second];
        if (c <= rem2) { rem2 -= c; val += gv; }
        else { val += gv * (rem2 / c); break; }
    }
    return (ll)ceil(val - 1e-9);
}

// --------------------------------------------------------------- lift solver
struct SolveResult {
    vector<int> S;
    double score1 = 0, score2 = 0, cost = 0;
    string source = "none";
    // certificate pieces
    double UB1_scaled = 0, lam1 = 0, lam2 = 0, chat = 0;
    // family stats
    double sigma_c = 0, theta = 0; int gadgets_ok = 0, gadgets_try = 0;
};

static SolveResult solve_lift(const HIN& G, const Cfg& C, const vector<char>& coreAlive,
                              const vector<vector<int>>& comps, Influence& inf,
                              GadgetFinder& gf, const vector<int>* kernel = nullptr) {
    SolveResult res;
    // ---- fallbacks -----------------------------------------------------
    vector<int> best; double bestSc = -1; string src = "none";
    for (int v = 0; v < G.n; v++)                               // singletons
        if (coreAlive[v] && !C.hasCons[G.type[v]] && G.cost[v] <= C.budget + 1e-12) {
            double s = inf.score({v}, 1);
            if (s > bestSc) { bestSc = s; best = {v}; src = "singleton"; }
        }
    // ---- per-component greedy closure lift ------------------------------
    for (auto& comp : comps) {
        // kernel-seeded component (hybrid mode): never pre-pruned
        bool kcomp = false;
        if (kernel && !kernel->empty())
            for (int v : comp) if (v == (*kernel)[0]) { kcomp = true; break; }
        // component-level pre-prune (Rule 2 analogue)
        double compUB = (double)inf.nT * (double)ub_component(inf, comp) /
                        (double)max<ll>(inf.col1.R, 1);
        if (!kcomp && compUB <= bestSc + 1e-12) continue;
        // seed candidates: top by singleton coverage density
        vector<int> cand = comp;
        sort(cand.begin(), cand.end(), [&](int a, int b) {
            return (double)inf.cov1[a].size() / G.cost[a] >
                   (double)inf.cov1[b].size() / G.cost[b];
        });
        int seedTry = (int)min<size_t>(cand.size(), 50);
        vector<int> U;                       // current closure (sorted)
        vector<char> inU(G.n, 0);
        long double cU = 0; ll covCnt = 0;
        static Stamp covSt; if (covSt.m.size() < (size_t)max<ll>(C.rr1, 1)) covSt.init((size_t)max<ll>(C.rr1, 1));
        covSt.fresh();
        auto marginal_exact = [&](int w, double& dCost) -> ll {
            if (!gf.ok[w]) return -1;
            dCost = 0;
            vector<int> newIds;
            for (int x : gf.K[w]) if (!inU[x]) {
                dCost += G.cost[x];
                for (int j : inf.cov1[x]) if (!covSt.test(j)) newIds.push_back(j);
            }
            sort_uniq(newIds);
            return (ll)newIds.size();
        };
        
        auto commit = [&](int w) {
            for (int x : gf.K[w]) if (!inU[x]) {
                inU[x] = 1; U.push_back(x); cU += G.cost[x];
                for (int j : inf.cov1[x]) if (!covSt.test(j)) { covSt.set(j); covCnt++; }
            }
        };
        // choose seed: the exact kernel when provided (hybrid), else the
        // best gadget by gain/cost ratio
        if (kcomp) {
            for (int x : *kernel) {
                if (inU[x]) continue;
                inU[x] = 1; U.push_back(x); cU += G.cost[x];
                for (int j : inf.cov1[x])
                    if (!covSt.test(j)) { covSt.set(j); covCnt++; }
            }
        } else {
            int seed = -1; double seedRatio = -1;
            for (int i = 0; i < seedTry; i++) {
                int v = cand[i]; gf.compute(v);
                if (!gf.ok[v]) continue;
                double dc; ll g = marginal_exact(v, dc);
                if (dc > C.budget + 1e-12 || g <= 0) continue;
                double r = (double)g / dc;
                if (r > seedRatio) { seedRatio = r; seed = v; }
            }
            if (seed < 0) continue;
            commit(seed);
        }
        // Two-phase growth: (A) hop-1 frontier by gain/cost; when A stalls,
        // (B) connector chains — BFS through the core up to HOPS hops, buy a
        // whole chain of gadgets whose UNION has the best gain/cost ratio.
        // Phase B is what lets the greedy cross zero-gain connector regions
        // (the path tax); each chain vertex is adjacent to its predecessor,
        // so the closure lemma keeps the union a connected r-com.
        const int HOPS = 4, TOPC = 30;
        while (true) {
            // ---- Phase A --------------------------------------------------
            while (true) {
                vector<int> fr;
                for (int u : U)
                    for (int e = G.off[u]; e < G.off[u + 1]; e++) {
                        int w = G.adj[e];
                        if (coreAlive[w] && !inU[w]) fr.push_back(w);
                    }
                sort_uniq(fr);
                int bw = -1; double bR = 0;
                for (int w : fr) {
                    gf.compute(w);
                    if (!gf.ok[w]) continue;
                    double dc; ll g = marginal_exact(w, dc);
                    if (g <= 0 || cU + dc > C.budget + 1e-12) continue;
                    double r = (double)g / max(dc, 1e-12);
                    if (r > bR) { bR = r; bw = w; }
                }
                if (bw < 0) break;
                commit(bw);
            }
            // ---- Phase B --------------------------------------------------
            static Stamp bfsSt; if (bfsSt.m.size() < (size_t)G.n) bfsSt.init(G.n);
            static vector<int> parent;
            if ((int)parent.size() < G.n) parent.assign(G.n, -1);
            bfsSt.fresh();
            vector<pair<int,int>> q; vector<int> reached;
            for (int u : U) bfsSt.set(u);
            for (int u : U)
                for (int e = G.off[u]; e < G.off[u + 1]; e++) {
                    int w = G.adj[e];
                    if (coreAlive[w] && !bfsSt.test(w)) {
                        bfsSt.set(w); parent[w] = -1;
                        q.push_back({w, 1}); reached.push_back(w);
                    }
                }
            for (size_t h = 0; h < q.size(); h++) {
                auto [x, d] = q[h];
                if (d >= HOPS) continue;
                for (int e = G.off[x]; e < G.off[x + 1]; e++) {
                    int w = G.adj[e];
                    if (coreAlive[w] && !inU[w] && !bfsSt.test(w)) {
                        bfsSt.set(w); parent[w] = x;
                        q.push_back({w, d + 1}); reached.push_back(w);
                    }
                }
            }
            sort(reached.begin(), reached.end(), [&](int a, int b) {
                return (double)inf.cov1[a].size() / G.cost[a] >
                       (double)inf.cov1[b].size() / G.cost[b];
            });
            static Stamp tmpV; if (tmpV.m.size() < (size_t)G.n) tmpV.init(G.n);
            int tried = 0, bestW = -1; double bestR = 0; vector<int> bestChain;
            for (int w : reached) {
                if (inf.cov1[w].empty()) break;              // density-sorted
                if (tried++ >= TOPC) break;
                vector<int> chain; int x = w; bool okc = true;
                while (x != -1) {
                    chain.push_back(x); x = parent[x];
                    if ((int)chain.size() > HOPS + 2) { okc = false; break; }
                }
                if (!okc) continue;
                reverse(chain.begin(), chain.end());          // U-adjacent first
                for (int cv : chain) { gf.compute(cv); if (!gf.ok[cv]) { okc = false; break; } }
                if (!okc) continue;
                double dc = 0; vector<int> newIds;
                tmpV.fresh();
                for (int cv : chain)
                    for (int x2 : gf.K[cv])
                        if (!inU[x2] && !tmpV.test(x2)) {
                            tmpV.set(x2); dc += G.cost[x2];
                            for (int j : inf.cov1[x2])
                                if (!covSt.test(j)) newIds.push_back(j);
                        }
                sort_uniq(newIds);
                ll g = (ll)newIds.size();
                if (g <= 0 || cU + dc > C.budget + 1e-12) continue;
                double r = (double)g / max(dc, 1e-12);
                if (r > bestR) { bestR = r; bestW = w; bestChain = chain; }
            }
            if (bestW < 0) break;
            for (int cv : bestChain) commit(cv);
        }
        double sc = (double)inf.nT * (double)covCnt / (double)max<ll>(inf.col1.R, 1);
        if (!U.empty() && sc > bestSc) { bestSc = sc; best = U; src = "lift"; }
    }
    // ---- best-gadget fallback (over computed gadgets) --------------------
    for (int v = 0; v < G.n; v++)
        if (gf.computed[v] && gf.ok[v] &&
            GadgetFinder::cost_of(G, gf.K[v]) <= C.budget + 1e-12) {
            double s = inf.score(gf.K[v], 1);
            if (s > bestSc) { bestSc = s; best = gf.K[v]; src = "gadget"; }
        }
    res.S = best; res.source = src;
    res.cost = GadgetFinder::cost_of(G, best);
    res.score1 = best.empty() ? 0 : inf.score(best, 1);
    res.score2 = best.empty() ? 0 : inf.score(best, 2);
    // family stats over computed gadgets
    double sc_ = 0, th_ = 0; int okc = 0, tr = 0;
    for (int v = 0; v < G.n; v++) if (gf.computed[v]) {
        tr++;
        if (gf.ok[v]) {
            okc++;
            double gcost = GadgetFinder::cost_of(G, gf.K[v]);
            sc_ = max(sc_, gcost); th_ = max(th_, gcost / G.cost[v]);
        }
    }
    res.sigma_c = sc_; res.theta = th_; res.gadgets_ok = okc; res.gadgets_try = tr;
    // ---- certificate ------------------------------------------------------
    ll ubRaw = 0;
    for (auto& comp : comps)
        ubRaw = max(ubRaw, min({ub_component(inf, comp),
                                ub_frac_knapsack(G, inf, comp, C.budget),
                                ub_marg_conditioned(G, inf, comp, C.budget)}));
    // singleton (unconstrained-type) solutions also live in comps; covered.
    res.UB1_scaled = (double)inf.nT * (double)ubRaw / (double)max<ll>(inf.col1.R, 1);
    res.lam1 = inf.nT * sqrt(log(2.0 / C.delta) / (2.0 * max<ll>(C.rr1, 1)));
    res.lam2 = inf.nT * sqrt(log(2.0 / C.delta) / (2.0 * max<ll>(C.rr2, 1)));
    double num = max(0.0, res.score2 - res.lam2);
    double den = res.UB1_scaled + res.lam1;
    res.chat = (den > 0) ? num / den : 0.0;
    return res;
}

// ----------------------------------------------------------- brute force
struct Brute {
    ll optRaw = -1; vector<int> argmax; bool ran = false; bool complete = true;
};
static Brute brute_force(const HIN& G, const Cfg& C, const vector<char>& /*coreAlive*/,
                         const vector<vector<int>>& comps, const Influence& inf) {
    Brute B;
    for (auto& comp : comps) {
        int m = (int)comp.size();
        if (m > 20) { B.complete = false; continue; }        // skip huge comps
        for (unsigned mask = 1; mask < (1u << m); mask++) {
            vector<int> S;
            double c = 0;
            for (int i = 0; i < m; i++) if (mask >> i & 1) { S.push_back(comp[i]); c += G.cost[comp[i]]; }
            if (c > C.budget + 1e-9) continue;
            string why;
            if (!verify_community(G, C, S, C.budget, why)) continue;
            ll cov = inf.covered(S, 1);
            if (cov > B.optRaw) { B.optRaw = cov; B.argmax = S; }
        }
    }
    B.ran = true;
    return B;
}

// ------------------------------------------------------- exact B&B solver
// Exact maximization of covered_1(S) over feasible communities (typed
// degrees, connectivity, budget) — the scalable replacement for the 2^m
// brute force. Design:
//   * connected-set enumeration: per-component root loop; inside a node the
//     frontier is processed with inline exclusions, so recursion depth is
//     bounded by |S| (budget), not |comp|;
//   * incremental protected peel of the allowed set (cascade removal with an
//     undo trail): any feasible superset of In lies inside the peeled allowed
//     set [Fact 1.1], so a peeled In vertex kills the subtree; excluding a
//     frontier vertex w prunes exactly the supersets containing w;
//   * upper bounds (valid on covered_1 by submodularity): conditioned-
//     marginal fractional knapsack over the In-reachable alive vertices on
//     small components, static density-prefix knapsack on large ones. Bounds
//     are refreshed lazily; staleness is one-sided (stale >= true), so
//     pruning stays valid;
//   * warm start from the lift solution (affects speed only, never the
//     optimum); the time limit makes the search anytime: truncUB records the
//     max bound over abandoned subtrees, certifying
//         OPT_raw <= max(bestRaw, truncUB)   when complete == false,
//         OPT_raw == bestRaw                 when complete == true.
static double secs_since(chrono::steady_clock::time_point t) {
    return chrono::duration<double>(chrono::steady_clock::now() - t).count();
}
static inline size_t fnv_ints(const vector<int>& v) {
    size_t h = 1469598103934665603ULL;
    for (int x : v) { h ^= (size_t)x + 0x9e3779b97f4a7c15ULL; h *= 1099511628211ULL; }
    return h;
}

// ------------------------------------------------------ algorithm variants
// Two public variants of the same exact MIMCS solver.  The baseline disables
// the three advanced optimization families.  Everything else is shared:
//   * fundamental exact enumeration (query anchoring, connected-frontier branch
//     candidate set, include/exclude partition with cumulative sibling
//     exclusions == unique-parent duplicate-free enumeration, exclusion
//     bookkeeping, In-state, fits(), incumbent recording, independent verifier);
//   * relational-core peel (shared preprocessing/decomposition);
//   * two-tier hot/cold RR influence-evaluation acceleration;
//   * closure-greedy warm start (primal heuristic; it can only set the
//     incumbent, and the incumbent reaches the search only via pruneThresh(),
//     which is read exclusively by Bounding-family code — so with bounding off
//     the warm start cannot prune anything);
//   * engineering infrastructure, T_max, eps = 0, no node cap.
//
// Family membership of each switch:
//   Advanced Reduction beyond R1
//     redAnchor      R2   anchored Dijkstra cost-ball + re-peel fixpoint
//     redCascade     R3   incremental protected-peel cascade on exclusion
//                         (exclusion bookkeeping always runs; only the cascade
//                          is disabled in the baseline)
//     redForcedProp  R4   forced-supporter propagation
//     redTwinSkip    R5a  twin-class branch skip / root skip (swap lemma)
//   Bounding
//     bounding       B1-B11, B14  every bound computation and bound-based prune
//                                 (ball, knapsack, boundary crossing, lazy
//                                  greedy, completion analysis, B0/B2, D_K,
//                                  connection LB, component pre-prune,
//                                  in-search truncation records)
//     bndTwinDedup   B12  one bound item per twin class
//   Advanced Branching priority
//     branchPriority N1-N3  MRV deficit branch-set selection + density/marginal
//                           candidate ranking + root ordering.  When false the
//                           branch set is the fundamental connected frontier and
//                           the next branch vertex is argmin over vertex id.
struct AlgoCfg {
    const char* name = "advanced_full";
    bool redAnchor = true, redCascade = true, redForcedProp = true, redTwinSkip = true;
    bool bounding = true, bndTwinDedup = true;
    bool branchPriority = true;
};
static const AlgoCfg ALGO_TABLE[] = {
    //  name                       rAnchor rCasc  rForce rTwin  bound  bTwin  brPrio
    { "advanced_full",             true,   true,  true,  true,  true,  true,  true  },
    { "baseline_enum",             false,  false, false, false, false, false, false },
};
static const int N_ALGOS = (int)(sizeof(ALGO_TABLE) / sizeof(ALGO_TABLE[0]));
static const AlgoCfg* parse_algo(const string& s) {
    for (int i = 0; i < N_ALGOS; i++) if (s == ALGO_TABLE[i].name) return &ALGO_TABLE[i];
    return nullptr;
}
static void print_algo_names(FILE* out) {
    for (int i = 0; i < N_ALGOS; i++) fprintf(out, "%s%s", i ? " " : "", ALGO_TABLE[i].name);
}
static inline const char* onoff(bool b) { return b ? "on" : "off"; }

struct ExactBnB {
    const HIN& G; const Cfg& C; const Influence& inf;
    ll nodeCap = 50'000'000;             // deprecated compatibility field; not enforced
    double timeCap = 120.0;
    double epsFrac = 0.0;               // eps-certified: prune at (1+eps)*incumbent
    bool requireConnIn = false;         // query mode: In may start disconnected
    const AlgoCfg* algo = &ALGO_TABLE[0];   // default: advanced_full
    // Lightweight counters for reporting which optimization paths executed.
    ll cntCascadeRemovals = 0, cntForcedInclusions = 0, cntTwinBranchSkips = 0;
    ll cntBoundCalls = 0, cntBoundPrunes = 0, cntCompletionPrunes = 0;
    ll cntMrvNodes = 0, cntRankNodes = 0, cntNeutralOrderNodes = 0;
    // results
    ll bestRaw = -1; vector<int> bestS; ll incumbentUpdates = 0;
    bool complete = true; ll nodes = 0; double truncUB = -1;
    // allowed-set (peel) state
    vector<char> aliveNow;
    vector<int> vcOff, aliveCnt, exTrail;
    // In state
    vector<char> inS; vector<int> In, inCnt;
    long double cIn = 0; int nUnsat = 0;
    // coverage state (collection 1)
    vector<char> cov; vector<int> covTrail; ll covCnt = 0;
    // per-component static knapsack prefix
    const vector<int>* curCompP = nullptr;
    vector<int> itemsV; vector<double> preCost, preVal;
    bool compBig = false; double cminComp = 1.0;
    size_t exactBallCap = 10000;         // test-overridable engineering cap
    ll ballTruncations = 0;
    ll coveringSkippedOnTrunc = 0, dkSkippedOnTrunc = 0;
    struct BItem { double d, m, c; int v; };   // density, marginal, cost, vertex
    // twin classes: vertices with identical (type, cost, core neighborhood,
    // cov1) are interchangeable in every feasible community — equal
    // constraint role, connectivity and Score_R1
    vector<int> twinCls; int nCls = 0;
    ll Rhot = 0; vector<int> hotEnd;    // two-tier split point per cov1 list
    vector<vector<int>> b0Pools; vector<int> b0Need;   // node pool export (B0)
    // Per-activation ball cache: In/cIn are frozen for one DFS call.
    // activation and exclusions only shrink aliveNow, so the entry-time
    // distance ball is a superset of every later reachable set — computed
    // lazily once per activation into a stack arena (sorted span), stale
    // entries filtered by aliveNow at use. dfs() saves/restores the frame.
    vector<int> ballArena;
    size_t ballLo = 0, ballHi = 0;
    bool ballValid = false, ballTruncC = false, ballSorted = false;
    Stamp st, gst, classSt;
    bool stop = false;
    chrono::steady_clock::time_point t0;

    ExactBnB(const HIN& g, const Cfg& c, const Influence& I) : G(g), C(c), inf(I) {}

    inline double pruneThresh() const {
        return (double)bestRaw * (1.0 + epsFrac) + 1e-9;
    }
    // same budget tolerance as verify_community
    inline bool fits(double c) const {
        return c <= C.budget + 1e-9 + 1e-12 * fabs(C.budget);
    }
    inline void tick() {
        nodes++;
        if ((nodes & 1023) == 0 && secs_since(t0) > timeCap) stop = true;
    }
    double margof(int v) const {
        ll m = 0;
        for (int j : inf.cov1[v]) if (!cov[j]) m++;
        return (double)m;
    }
    // ---- two-tier coverage (deterministic acceleration) ---------------------
    // RR ids are partitioned into a hot prefix (id < Rhot) and a cold rest.
    // covered_1 is additive across the partition, so a fresh hot marginal
    // plus the static cold list size is a valid per-item upper bound at ~1/8
    // of the scan cost; only the knapsack head is refreshed at full
    // resolution. cov1 lists are id-sorted, so the hot part of each list is
    // its prefix: hotEnd[v] is the only extra state.
    double margHot(int v) const {
        const auto& L = inf.cov1[v];
        ll m = 0;
        for (int i = 0; i < hotEnd[v]; i++) if (!cov[L[i]]) m++;
        return (double)m;
    }
    inline double upperVal(int v) const {   // fresh hot + static cold
        return margHot(v) + (double)(inf.cov1[v].size() - (size_t)hotEnd[v]);
    }
    // static prefix knapsack over the current component, remaining budget beta
    double static_query(double beta) const {
        if (beta <= 0 || itemsV.empty()) return 0;
        size_t t = (size_t)(upper_bound(preCost.begin(), preCost.end(), beta + 1e-12)
                            - preCost.begin()) - 1;
        double val = preVal[t];
        if (t < itemsV.size()) {
            double c = G.cost[itemsV[t]], v = (double)inf.cov1[itemsV[t]].size();
            val += v * ((beta - preCost[t]) / c);
        }
        return val;
    }
    // Record a certified bound for an abandoned subtree. Uses the strongest
    // cheap bound available: the full node bound when In is nonempty, and an
    // alive-filtered (post-exclusion) static knapsack at root level — the
    // stale prefix would count vertices already excluded from this comp.
    void record_trunc(double resNeed = 0, double resCredit = 0, double cap = 1e300) {
        // Bounding OFF: no in-search bound is ever computed, not even for the
        // anytime certificate.  certifiedUBraw() then reports +inf so that the
        // ROOT upper bound (computed outside the B&B and identical in both
        // variants) governs the reported certified_UB.  Never claims optimality.
        if (!algo->bounding) return;
        double b;
        if (!In.empty()) {
            b = bound_now(resNeed, resCredit);
        } else {
            double rem = C.budget, val = 0;
            for (int v : itemsV) {
                if (!aliveNow[v]) continue;
                double m = (double)inf.cov1[v].size(), c = G.cost[v];
                if (c <= rem) { rem -= c; val += m; }
                else { val += m * (rem / c); break; }
            }
            b = val;
        }
        truncUB = max(truncUB, min(b, cap));
    }
    // Distance-filtered ball cached per DFS activation: every vertex
    // of a feasible superset S of In lies within floor(beta/cmin) hops of In
    // (the connecting path runs through S \ In, each hop costing >= cmin)
    void ensure_ball(double beta) {
        if (ballValid) return;
        static thread_local vector<int> bq, dep;
        int D = (int)(beta / max(cminComp, 1e-12) + 1e-9);
        const size_t CAP = max<size_t>(exactBallCap, 1);
        st.fresh(); bq.clear(); dep.clear();
        bool tr = false;
        for (int v : In) { st.set(v); bq.push_back(v); dep.push_back(0); }
        if (bq.size() > CAP) tr = true;
        for (size_t h = 0; h < bq.size() && !tr; h++) {
            int v = bq[h];
            if (dep[h] >= D) continue;
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e];
                if (aliveNow[u] && !st.test(u)) {
                    st.set(u); bq.push_back(u); dep.push_back(dep[h] + 1);
                    if (bq.size() > CAP) { tr = true; break; }
                }
            }
        }
        ballLo = ballArena.size();
        ballArena.insert(ballArena.end(), bq.begin(), bq.end());
        ballHi = ballArena.size();
        ballTruncC = tr; ballValid = true;
        if (tr) ballTruncations++;
        ballSorted = false;       // sorted lazily, only if the walk needs it
    }
    // Valid UB on max covered_1 over feasible supersets of In in the subtree.
    // completion_analysis supplies a jointly certified reservation envelope:
    // every completion has a role assignment costing >= resNeed whose summed
    // marginal is <= resCredit.  The remaining packing gets beta-resNeed.
    double bound_now(double resNeed = 0, double resCredit = 0) {
        double beta = max(0.0, C.budget - (double)cIn);
        double beta2 = max(0.0, beta - resNeed);
        static thread_local vector<int> cand, bq, dep;
        cand.clear();
        bool truncated = false;
        if (In.empty()) {
            if (compBig) return (double)covCnt + static_query(beta);
            for (int v : *curCompP) if (aliveNow[v]) cand.push_back(v);
        } else {
            ensure_ball(beta);
            truncated = ballTruncC;
        }
        // fresh-marginal items inside the ball / reachable set; twin classes
        // contribute once (all members share one coverage list, so a second
        // member adds constraint support but zero new coverage)
        static thread_local vector<BItem> its;
        its.clear();
        classSt.fresh();
        auto push_item = [&](int v) {
            if (!aliveNow[v] || inS[v]) return;      // stale ball entries skipped
            if (algo->bndTwinDedup) {
                if (classSt.test(twinCls[v])) return;
                classSt.set(twinCls[v]);
            }
            double m = upperVal(v);          // hot-fresh + cold-static (valid UB)
            if (m > 0) its.push_back({m / G.cost[v], m, G.cost[v], v});
        };
        if (In.empty()) for (int v : cand) push_item(v);
        else for (size_t i = ballLo; i < ballHi; i++) push_item(ballArena[i]);
        sort(its.begin(), its.end(),
             [](const BItem& a, const BItem& b) { return a.d > b.d; });
        // exact full-resolution refresh of the knapsack head — the head is
        // where the budget is spent; tail items keep their upper values
        {
            size_t K = its.size() <= 128 ? its.size() : (size_t)64;
            bool chg = false;
            for (size_t i = 0; i < K; i++) {
                double m = margof(its[i].v);
                if (m != its[i].m) { its[i].m = m; its[i].d = m / its[i].c; chg = true; }
            }
            if (chg) {
                its.erase(remove_if(its.begin(), its.end(),
                                    [](const BItem& x) { return x.m <= 0; }), its.end());
                sort(its.begin(), its.end(),
                     [](const BItem& a, const BItem& b) { return a.d > b.d; });
            }
        }
        // boundary-crossing: if the ball was truncated, vertices beyond it can
        // still join S; each contributes at most its static cover at its
        // static density, so they enter the knapsack as static items (walk the
        // per-comp density-sorted list, skipping ball members via st)
        size_t sp = itemsV.size();
        double topOut = 0;
        auto in_ball = [&](int v) {
            if (!ballSorted) {
                sort(ballArena.begin() + ballLo, ballArena.begin() + ballHi);
                ballSorted = true;
            }
            return binary_search(ballArena.begin() + ballLo,
                                 ballArena.begin() + ballHi, v);
        };
        if (truncated) {
            sp = 0;
            while (sp < itemsV.size() && in_ball(itemsV[sp])) sp++;
            if (sp < itemsV.size())
                topOut = (double)inf.cov1[itemsV[sp]].size() / G.cost[itemsV[sp]];
        }
        // (1) fractional knapsack merged across ball items and outside items
        double rem = beta2, val = 0;
        size_t ip = 0, sq = sp;
        while (rem > 1e-12 && (ip < its.size() || sq < itemsV.size())) {
            double dI = (ip < its.size()) ? its[ip].d : -1.0;
            double dS = -1.0, mS = 0, cS = 0;
            if (sq < itemsV.size()) {
                int u = itemsV[sq];
                mS = (double)inf.cov1[u].size(); cS = G.cost[u]; dS = mS / cS;
            }
            double m, c;
            if (dI >= dS) { m = its[ip].m; c = its[ip].c; ip++; }
            else {
                m = mS; c = cS;
                do { sq++; } while (sq < itemsV.size() && in_ball(itemsV[sq]));
            }
            if (c <= rem) { rem -= c; val += m; }
            else { val += m * (rem / c); break; }
        }
        double bnd = (double)covCnt + resCredit + val;
        if (bnd <= pruneThresh() || its.empty()) return bnd;
        // (2) overlap-aware lazy-greedy refinement: after committing a greedy
        // prefix P, any feasible T obeys
        //   cov(In u T) <= cov(In u P) + beta * maxdens(. | In u P)
        // (submodularity + cost(T) <= beta). Stale PQ keys upper-bound fresh
        // densities (marginals only shrink), so the PQ top is a valid maxdens;
        // out-of-ball items are covered by their static density topOut.
        gst.fresh();
        priority_queue<pair<double,int>> pq;
        for (auto& it : its) pq.push({it.d, it.v});
        double V = 0; int steps = 0;
        int maxSteps = min(48, (int)(beta / max(cminComp, 1e-12)) + 4);
        while (!pq.empty() && steps < maxSteps) {
            auto pr = pq.top(); pq.pop();
            int v = pr.second;
            double m = 0;
            for (int j : inf.cov1[v]) if (!cov[j] && !gst.test(j)) m += 1.0;
            double fd = m / G.cost[v];
            if (fd <= 1e-12) {
                if (pq.empty()) bnd = min(bnd, (double)covCnt + resCredit + V + beta2 * topOut);
                continue;
            }
            if (!pq.empty() && fd + 1e-12 < pq.top().first) { pq.push({fd, v}); continue; }
            for (int j : inf.cov1[v]) if (!cov[j] && !gst.test(j)) { gst.set(j); V += 1.0; }
            steps++;
            double topd = pq.empty() ? 0.0 : pq.top().first;
            bnd = min(bnd, (double)covCnt + resCredit + V + beta2 * max(topd, topOut));
            if (bnd <= pruneThresh()) break;
        }
        return bnd;
    }
    // ---- In maintenance (typed-degree deficits, incremental) ---------------
    void include(int w) {
        inS[w] = 1; In.push_back(w); cIn += G.cost[w];
        for (int j : inf.cov1[w])
            if (!cov[j]) { cov[j] = 1; covTrail.push_back(j); covCnt++; }
        auto& csW = C.consOf[G.type[w]]; int baseW = vcOff[w];
        for (size_t i = 0; i < csW.size(); i++) inCnt[baseW + (int)i] = 0;
        for (int e = G.off[w]; e < G.off[w + 1]; e++) {
            int u = G.adj[e]; if (!inS[u]) continue;
            for (size_t i = 0; i < csW.size(); i++)
                if (csW[i].first == G.type[u]) inCnt[baseW + (int)i]++;
            auto& csU = C.consOf[G.type[u]]; int baseU = vcOff[u];
            for (size_t i = 0; i < csU.size(); i++)
                if (csU[i].first == G.type[w] &&
                    ++inCnt[baseU + (int)i] == csU[i].second) nUnsat--;
        }
        for (size_t i = 0; i < csW.size(); i++)
            if (inCnt[baseW + (int)i] < csW[i].second) nUnsat++;
    }
    void undo_include(int w, size_t covMark) {
        auto& csW = C.consOf[G.type[w]]; int baseW = vcOff[w];
        for (size_t i = 0; i < csW.size(); i++)
            if (inCnt[baseW + (int)i] < csW[i].second) nUnsat--;
        inS[w] = 0; In.pop_back(); cIn -= G.cost[w];
        for (int e = G.off[w]; e < G.off[w + 1]; e++) {
            int u = G.adj[e]; if (!inS[u]) continue;
            auto& csU = C.consOf[G.type[u]]; int baseU = vcOff[u];
            for (size_t i = 0; i < csU.size(); i++)
                if (csU[i].first == G.type[w] &&
                    inCnt[baseU + (int)i]-- == csU[i].second) nUnsat++;
        }
        while (covTrail.size() > covMark) {
            cov[covTrail.back()] = 0; covTrail.pop_back(); covCnt--;
        }
    }
    // ---- allowed-set maintenance (incremental peel with undo) ---------------
    inline bool alive_viol(int v) const {
        auto& cs = C.consOf[G.type[v]]; int base = vcOff[v];
        for (size_t i = 0; i < cs.size(); i++)
            if (aliveCnt[base + (int)i] < cs[i].second) return true;
        return false;
    }
    bool exclude_cascade(int w) {           // false if an In vertex was peeled
        // Removal must be ATOMIC (dead flag + neighbor decrements together,
        // in trail order): marking at push time lets pop order invert trail
        // order, and then undo (reverse trail) re-increments counters that
        // were never decremented. Hence peel_core's pattern: pop, re-check
        // violation, then remove-and-decrement in one step.
        if (!aliveNow[w]) return true;
        // Split by variant: removeV() is the EXCLUDE half of the include/exclude
        // enumeration partition and is correctness-critical — it runs in every
        // variant, and its aliveCnt decrements must happen because the forced
        // propagation (aliveCnt == k) and the MRV pool size (aliveCnt - inCnt)
        // read those counters.  Only the CASCADE (seeding and draining stk, and
        // hence the In-vertex-death signal) is the Reduction-family technique.
        // With the cascade off, w is never an In vertex (branch candidates
        // satisfy !inS[w]), so okIn stays vacuously true.
        const bool cascade = algo->redCascade;
        bool okIn = true;
        static thread_local vector<int> stk;
        stk.clear();
        auto removeV = [&](int v) {
            aliveNow[v] = 0; exTrail.push_back(v);
            if (inS[v]) okIn = false;
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e]; if (!aliveNow[u]) continue;
                auto& cs = C.consOf[G.type[u]]; int base = vcOff[u];
                bool hit = false;
                for (size_t i = 0; i < cs.size(); i++)
                    if (cs[i].first == G.type[v]) { aliveCnt[base + (int)i]--; hit = true; }
                if (cascade && hit && alive_viol(u)) stk.push_back(u);
            }
        };
        removeV(w);
        while (!stk.empty()) {
            int v = stk.back(); stk.pop_back();
            if (!aliveNow[v] || !alive_viol(v)) continue;   // re-check at pop
            cntCascadeRemovals++;
            removeV(v);
        }
        return okIn;
    }
    void undo_exclusions(size_t mark) {     // reverse removal order restores counts
        while (exTrail.size() > mark) {
            int v = exTrail.back(); exTrail.pop_back();
            aliveNow[v] = 1;
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e]; if (!aliveNow[u]) continue;
                auto& cs = C.consOf[G.type[u]]; int base = vcOff[u];
                for (size_t i = 0; i < cs.size(); i++)
                    if (cs[i].first == G.type[v]) aliveCnt[base + (int)i]++;
            }
        }
    }
#ifdef PARANOID
    void check_alive(const char* tag) const {
        for (int v = 0; v < G.n; v++) if (aliveNow[v]) {
            auto& cs = C.consOf[G.type[v]]; int base = vcOff[v];
            for (size_t i = 0; i < cs.size(); i++) {
                int t = 0;
                for (int e = G.off[v]; e < G.off[v + 1]; e++)
                    if (aliveNow[G.adj[e]] && G.type[G.adj[e]] == cs[i].first) t++;
                if (t != aliveCnt[base + (int)i]) {
                    fprintf(stderr, "[PARANOID %s] v=%d slot=%zu cnt=%d true=%d\n",
                            tag, v, i, aliveCnt[base + (int)i], t);
                    abort();
                }
            }
        }
    }
#endif
    bool in_connected() {                // BFS within In (query mode only)
        if (In.size() <= 1) return true;
        st.fresh();
        static thread_local vector<int> q2;
        q2.clear(); q2.push_back(In[0]); st.set(In[0]);
        size_t seen = 1;
        for (size_t h = 0; h < q2.size(); h++) {
            int v = q2[h];
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e];
                if (inS[u] && !st.test(u)) { st.set(u); q2.push_back(u); seen++; }
            }
        }
        return seen == In.size();
    }
    // connection lower bound (query mode): cheapest interior cost linking
    // In's first fragment to its farthest fragment within the alive set
    double connect_lb() {
        static thread_local vector<double> dist;
        static thread_local vector<int> frag;
        if ((int)dist.size() < G.n) { dist.assign(G.n, 1e300); frag.assign(G.n, -1); }
        static thread_local vector<int> touched, dtouch;
        touched.clear(); dtouch.clear();
        int nf = 0;
        for (int s : In) {
            if (frag[s] >= 0) continue;
            static thread_local vector<int> bq;
            bq.clear(); bq.push_back(s); frag[s] = nf; touched.push_back(s);
            for (size_t h = 0; h < bq.size(); h++) {
                int v = bq[h];
                for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                    int u = G.adj[e];
                    if (inS[u] && frag[u] < 0) {
                        frag[u] = nf; touched.push_back(u); bq.push_back(u);
                    }
                }
            }
            nf++;
        }
        double lb = 0;
        if (nf > 1) {
            priority_queue<pair<double,int>, vector<pair<double,int>>,
                           greater<pair<double,int>>> pq;
            for (int s : In) if (frag[s] == 0) { dist[s] = 0; dtouch.push_back(s); pq.push({0, s}); }
            static thread_local vector<double> best;
            best.assign(nf, 1e300); best[0] = 0;
            int remaining = nf - 1;
            while (!pq.empty() && remaining > 0) {
                auto [d, v] = pq.top(); pq.pop();
                if (d > dist[v]) continue;
                if (frag[v] > 0 && best[frag[v]] > 1e299) { best[frag[v]] = d; remaining--; }
                for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                    int u = G.adj[e];
                    if (!aliveNow[u]) continue;
                    double nd = d + (inS[u] ? 0.0 : G.cost[u]);
                    if (nd < dist[u] - 1e-12) {
                        if (dist[u] > 1e299) dtouch.push_back(u);
                        dist[u] = nd; pq.push({nd, u});
                    }
                }
            }
            for (int f = 1; f < nf; f++) lb = max(lb, best[f]);
            if (lb > 1e299) lb = 1e300;         // unreachable fragment: prune
        }
        for (int v : touched) frag[v] = -1;
        for (int v : dtouch) dist[v] = 1e300;
        return lb;
    }
    // ---- completion analysis (node-level budget certificates) ----------------
    // Two valid lower bounds on the extra spend of any feasible completion:
    //  (a) per-vertex: worst deficient In vertex's cheapest typed completion
    //      (max across vertices — helpers may be shared, so max, not sum);
    //  (b) aggregated (paper's Rule 6): per type A, total demand D_A over all
    //      deficient In vertices, capped by the best single-supporter cover
    //      Dmax_A, forces >= ceil(D_A/Dmax_A) type-A additions from the union
    //      pool; distinct types have disjoint pools, so the costs add.
    // Returns false to prune.  The reservation is a certified rectangle over
    // the SAME legal role-assignment family: resNeed is its minimum cost and
    // resCredit its maximum summed marginal.  Thus every feasible completion
    // is covered even though the two extrema may use different identities.
    bool completion_analysis(double& resNeed, double& resCredit) {
        resNeed = 0; resCredit = 0;
        static thread_local vector<double> cheap;
        static thread_local vector<int> cntW, touched, nNeed, mNeed;
        static thread_local vector<double> Dm;
        static thread_local vector<vector<int>> pool;
        if ((int)cntW.size() < G.n) cntW.assign(G.n, 0);
        if ((int)Dm.size() < G.ntypes) {
            Dm.assign(G.ntypes, 0); pool.assign(G.ntypes, {});
            nNeed.assign(G.ntypes, 0); mNeed.assign(G.ntypes, 0);
        }
        for (int t = 0; t < G.ntypes; t++) {
            Dm[t] = 0; pool[t].clear(); nNeed[t] = 0; mNeed[t] = 0;
        }
        touched.clear();
        double need1 = 0;
        for (int v : In) {
            auto& cs = C.consOf[G.type[v]]; int base = vcOff[v];
            double Lv = 0; bool defic = false;
            for (size_t i = 0; i < cs.size(); i++) {
                int d = cs[i].second - inCnt[base + (int)i];
                // duplicate constraints on the same neighbor type share one
                // helper pool: only the largest deficit binds
                bool dominated = false;
                for (size_t j = 0; j < cs.size(); j++)
                    if (j != i && cs[j].first == cs[i].first) {
                        int dj = cs[j].second - inCnt[base + (int)j];
                        if (dj > d || (dj == d && j < i)) { dominated = true; break; }
                    }
                if (d <= 0 || dominated) continue;
                defic = true;
                int t = cs[i].first;
                Dm[t] += d;
                cheap.clear();
                for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                    int u = G.adj[e];
                    if (aliveNow[u] && !inS[u] && G.type[u] == t) {
                        cheap.push_back(G.cost[u]);
                        if (cntW[u]++ == 0) pool[t].push_back(u);
                        touched.push_back(u);
                    }
                }
                if ((int)cheap.size() < d) { Lv = 1e300; break; }
                nth_element(cheap.begin(), cheap.begin() + (d - 1), cheap.end());
                for (int x = 0; x < d; x++) Lv += cheap[x];
            }
            if (defic) need1 = max(need1, Lv);
        }
        bool feasible = true;
        for (int t = 0; t < G.ntypes && feasible; t++) {
            if (Dm[t] <= 0) continue;
            int dmax = 0;
            for (int w : pool[t]) dmax = max(dmax, cntW[w]);
            if (dmax == 0) { feasible = false; break; }
            int nA = ((int)(Dm[t] + 0.5) + dmax - 1) / dmax;
            if ((int)pool[t].size() < nA) { feasible = false; break; }
            nNeed[t] = nA;
        }
        // Export pool structure for the covering-knapsack bound;
        // consumed once per node, before any child search runs
        b0Pools.clear(); b0Need.clear();
        for (int t = 0; t < G.ntypes; t++) {
            if (Dm[t] <= 0 || pool[t].empty()) continue;
            int dmax = 0;
            for (int w : pool[t]) dmax = max(dmax, cntW[w]);
            if (dmax <= 0) continue;
            b0Pools.push_back(pool[t]);
            b0Need.push_back(nNeed[t]);
        }
        // ---- level 2: induced obligations of the forced level-1 picks ------
        // Every type-A level-1 pick w carries residual demands rho_w(B) vs In;
        // taking the pool-minimum per (A,B) makes the charge valid for ANY
        // choice of picks. Aggregate induced B-demand, subtract what level-1's
        // own type-B picks can serve (sharing cap D2_B = max per-B-vertex
        // adjacency into the demanding pools), and price the remainder with
        // the cheapest DISTINCT type-B supporters (level-1 charges excluded).
        if (feasible) {
            static thread_local vector<double> ind;        // induced demand per type
            static thread_local vector<vector<int>> l2pool;
            if ((int)ind.size() < G.ntypes) { ind.assign(G.ntypes, 0); l2pool.assign(G.ntypes, {}); }
            for (int t = 0; t < G.ntypes; t++) { ind[t] = 0; l2pool[t].clear(); }
            static thread_local vector<int> l2cnt, l2touch;
            if ((int)l2cnt.size() < G.n) l2cnt.assign(G.n, 0);
            l2touch.clear();
            for (int t = 0; t < G.ntypes; t++) {
                if (Dm[t] <= 0 || pool[t].empty()) continue;
                int dmax = 0;
                for (int w : pool[t]) dmax = max(dmax, cntW[w]);
                if (dmax <= 0) continue;
                int nA = nNeed[t];
                // rho_min per induced type B over this pool, and level-2 pools
                static thread_local vector<int> rhoMin;
                if ((int)rhoMin.size() < G.ntypes) rhoMin.assign(G.ntypes, 0);
                for (int b2 = 0; b2 < G.ntypes; b2++) rhoMin[b2] = INT32_MAX;
                bool anyCons = !C.consOf[G.type[pool[t][0]]].empty();
                if (!anyCons) continue;
                for (int w : pool[t]) {
                    auto& cs = C.consOf[G.type[w]];
                    static thread_local vector<int> have;
                    if ((int)have.size() < G.ntypes) have.assign(G.ntypes, 0);
                    for (auto& pr : cs) have[pr.first] = 0;
                    for (int e = G.off[w]; e < G.off[w + 1]; e++) {
                        int u = G.adj[e];
                        if (inS[u]) have[G.type[u]]++;
                        else if (aliveNow[u]) {
                            // level-2 supporter pool + sharing count
                            if (l2cnt[u]++ == 0) l2pool[G.type[u]].push_back(u);
                            l2touch.push_back(u);
                        }
                    }
                    for (size_t i = 0; i < cs.size(); i++) {
                        int d = cs[i].second - have[cs[i].first];
                        bool dom = false;
                        for (size_t j = 0; j < cs.size(); j++)
                            if (j != i && cs[j].first == cs[i].first &&
                                (cs[j].second > cs[i].second ||
                                 (cs[j].second == cs[i].second && j < i)))
                                { dom = true; break; }
                        if (dom) continue;
                        rhoMin[cs[i].first] = min(rhoMin[cs[i].first], max(0, d));
                    }
                }
                for (int b2 = 0; b2 < G.ntypes; b2++)
                    if (rhoMin[b2] != INT32_MAX && rhoMin[b2] > 0)
                        ind[b2] += (double)nA * rhoMin[b2];
            }
            for (int b2 = 0; b2 < G.ntypes && feasible; b2++) {
                if (ind[b2] <= 0) continue;
                // supply from level-1 type-b2 picks, capped by sharing
                int d2 = 0;
                for (int u : l2pool[b2]) d2 = max(d2, l2cnt[u]);
                if (d2 <= 0) { feasible = false; break; }   // demand, no supporters
                double served = 0;
                if (Dm[b2] > 0 && !pool[b2].empty()) {
                    int dmaxB = 0;
                    for (int w : pool[b2]) dmaxB = max(dmaxB, cntW[w]);
                    if (dmaxB > 0) {
                        int nB = ((int)(Dm[b2] + 0.5) + dmaxB - 1) / dmaxB;
                        served = (double)nB * d2;
                    }
                }
                double rem = ind[b2] - served;
                if (rem <= 0) continue;
                mNeed[b2] = (int)((rem + d2 - 1) / d2);
            }
            for (int u : l2touch) l2cnt[u] = 0;

            // Joint identity pricing.  For each type, partition candidates into
            // direct-only, overlap, and induced-only groups.  Enumerating how
            // many overlap vertices take each role avoids prematurely fixing
            // the cheapest direct identities and then excluding them from the
            // induced role.  This is a finite combinatorial calculation, not an
            // LP/MIP relaxation.
            static thread_local vector<unsigned char> role;
            static thread_local vector<double> directOnly, both, inducedOnly;
            static thread_local vector<double> directGain, bothGain, inducedGain;
            if ((int)role.size() < G.n) role.assign(G.n, 0);
            double need2 = 0;
            for (int t = 0; t < G.ntypes && feasible; t++) {
                int nA = nNeed[t], mA = mNeed[t];
                if (nA == 0 && mA == 0) continue;
                for (int u : pool[t]) role[u] |= 1;
                for (int u : l2pool[t]) role[u] |= 2;
                directOnly.clear(); both.clear(); inducedOnly.clear();
                directGain.clear(); bothGain.clear(); inducedGain.clear();
                for (int u : pool[t]) {
                    if (role[u] == 3) {
                        both.push_back(G.cost[u]); bothGain.push_back(upperVal(u));
                    } else {
                        directOnly.push_back(G.cost[u]); directGain.push_back(upperVal(u));
                    }
                }
                for (int u : l2pool[t])
                    if (role[u] == 2) {
                        inducedOnly.push_back(G.cost[u]); inducedGain.push_back(upperVal(u));
                    }
                for (int u : pool[t]) role[u] = 0;
                for (int u : l2pool[t]) role[u] = 0;

                int directCount = (int)directOnly.size();
                int bothCount = (int)both.size();
                int inducedCount = (int)inducedOnly.size();
                auto makePrefix = [](vector<double>& a, int k, bool descending) {
                    k = min(k, (int)a.size());
                    if (k <= 0) { a.clear(); return; }
                    if (descending)
                        partial_sort(a.begin(), a.begin() + k, a.end(), greater<double>());
                    else
                        partial_sort(a.begin(), a.begin() + k, a.end());
                    a.resize(k);
                    for (int i = 1; i < k; i++) a[i] += a[i - 1];
                };
                makePrefix(directOnly, nA, false);
                makePrefix(both, nA + mA, false);
                makePrefix(inducedOnly, mA, false);
                makePrefix(directGain, nA, true);
                makePrefix(bothGain, nA + mA, true);
                makePrefix(inducedGain, mA, true);
                auto pref = [](const vector<double>& a, int k) {
                    return k == 0 ? 0.0 : a[k - 1];
                };
                double bestJoint = 1e300;
                double maxJointGain = 0;
                int rLo = max(0, nA - directCount);
                int rHi = min(nA, bothCount);
                for (int r = rLo; r <= rHi; r++) {
                    int sLo = max(0, mA - inducedCount);
                    int sHi = min(mA, bothCount - r);
                    for (int s = sLo; s <= sHi; s++) {
                        double z = pref(directOnly, nA - r) +
                                   pref(both, r + s) +
                                   pref(inducedOnly, mA - s);
                        double g = pref(directGain, nA - r) +
                                   pref(bothGain, r + s) +
                                   pref(inducedGain, mA - s);
                        bestJoint = min(bestJoint, z);
                        maxJointGain = max(maxJointGain, g);
                    }
                }
                if (bestJoint >= 1e299) feasible = false;
                else { need2 += bestJoint; resCredit += maxJointGain; }
            }

            if (!feasible || !fits((double)cIn + max(need1, need2))) {
                for (int u : touched) cntW[u] = 0;
                resNeed = 0; resCredit = 0;
                return false;
            }
            resNeed = need2;
        }
        for (int u : touched) cntW[u] = 0;
        return feasible;
    }
    // ---- B2: budget-priced covering knapsack -------------------------------
    // Relaxation over the ball's twin-class units:
    //   max sum m_c x_c   s.t.  sum c x <= beta,  per pool: units >= n_A
    // with twin classes expanded to units (first member carries the class
    // marginal, extras carry zero gain but one covering unit and one cost).
    // Dualize only the budget row at price lam >= 0: pools are disjoint, so
    // the inner separates and is greedy-exact; any lam gives a valid UB by
    // weak duality. L(lam) is convex; ternary search on the density grid.
    double bound_covering() {
        if (!algo->bounding) return 1e300;   // defence in depth: b0Pools may be stale
        if (In.empty() || b0Pools.empty()) return 1e300;
        double beta = max(0.0, C.budget - (double)cIn);
        ensure_ball(beta);
        // Correctness guard: B2 requires the complete candidate/pool domain.
        // A truncated ball can omit feasible score items or required supporters,
        // making the computed value too small and therefore unsafe for pruning.
        // Returning the no-information sentinel keeps the safe bound_now()
        // result as the active upper bound.
        if (ballTruncC) { coveringSkippedOnTrunc++; return 1e300; }
        /*
         * Legacy backup (intentionally not compiled or called): the earlier
         * formulation omitted the guard above and continued with only the
         * stored portion of a truncated ball. That version is retained here as
         * a design note only; enabling it can underestimate the branch optimum.
         */
        // vertex -> pool id (pools are small; touched-reset array)
        static thread_local vector<int> poolId, ptouch;
        if ((int)poolId.size() < G.n) poolId.assign(G.n, -1);
        ptouch.clear();
        for (size_t p = 0; p < b0Pools.size(); p++)
            for (int w : b0Pools[p]) { poolId[w] = (int)p; ptouch.push_back(w); }
        // unit groups per twin class present in the ball
        struct UG { double m, c; int pool, extra; };
        static thread_local vector<UG> ug;
        static thread_local vector<int> clsPos, ctouch;
        if ((int)clsPos.size() < max(nCls, 1)) clsPos.assign(max(nCls, 1), -1);
        ug.clear(); ctouch.clear();
        for (size_t i = ballLo; i < ballHi; i++) {
            int v = ballArena[i];
            if (!aliveNow[v] || inS[v]) continue;
            int cl = twinCls[v];
            if (clsPos[cl] < 0) {
                clsPos[cl] = (int)ug.size(); ctouch.push_back(cl);
                ug.push_back({upperVal(v), G.cost[v], poolId[v], 0});
            } else ug[clsPos[cl]].extra++;
        }
        for (int w : ptouch) poolId[w] = -1;
        for (int c0 : ctouch) clsPos[c0] = -1;
        // free part: prefix arrays over density-sorted first units
        static thread_local vector<double> fd, fM, fC;
        fd.clear();
        static thread_local vector<pair<double,pair<double,double>>> fu;
        fu.clear();
        static thread_local vector<vector<pair<double,double>>> pu;   // per pool (m,c) first units
        static thread_local vector<vector<pair<double,int>>> pex;     // per pool (c, extra count)
        pu.assign(b0Pools.size(), {}); pex.assign(b0Pools.size(), {});
        for (auto& g : ug) {
            if (g.pool < 0) { if (g.m > 0) fu.push_back({g.m / g.c, {g.m, g.c}}); }
            else {
                pu[g.pool].push_back({g.m, g.c});
                if (g.extra > 0) pex[g.pool].push_back({g.c, g.extra});
            }
        }
        sort(fu.begin(), fu.end(), greater<>());
        fM.assign(fu.size() + 1, 0); fC.assign(fu.size() + 1, 0);
        for (size_t i = 0; i < fu.size(); i++) {
            fd.push_back(fu[i].first);
            fM[i + 1] = fM[i] + fu[i].second.first;
            fC[i + 1] = fC[i] + fu[i].second.second;
        }
        // L(lam)
        static thread_local vector<double> prof;
        auto evalL = [&](double lam) -> double {
            // free: items with density > lam
            size_t k = (size_t)(lower_bound(fd.begin(), fd.end(), lam,
                                            greater<double>()) - fd.begin());
            double L = lam * beta + fM[k] - lam * fC[k];
            for (size_t p = 0; p < b0Pools.size(); p++) {
                prof.clear();
                double pos = 0; int npos = 0;
                for (auto& q : pu[p]) {
                    double r = q.first - lam * q.second;
                    if (r > 0) { pos += r; npos++; }
                    else prof.push_back(r);
                }
                for (auto& q : pex[p])
                    for (int x = 0; x < q.second; x++) prof.push_back(-lam * q.first);
                int need = b0Need[p] - npos;
                if (need > 0) {
                    if ((int)prof.size() < need) return -1e300;   // Farkas: infeasible
                    nth_element(prof.begin(), prof.begin() + (need - 1), prof.end(),
                                greater<double>());
                    for (int x = 0; x < need; x++) pos += prof[x];
                }
                L += pos;
            }
            return L;
        };
        // candidate lambda grid: all first-unit densities + 0
        static thread_local vector<double> grid;
        grid.clear(); grid.push_back(0.0);
        for (auto& g : ug) if (g.m > 0) grid.push_back(g.m / g.c);
        sort(grid.begin(), grid.end());
        grid.erase(unique(grid.begin(), grid.end()), grid.end());
        int lo = 0, hi = (int)grid.size() - 1;
        double best = 1e300;
        while (hi - lo > 2) {                    // convex: ternary on the grid
            int m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3;
            double L1 = evalL(grid[m1]), L2 = evalL(grid[m2]);
            if (L1 <= -1e299 || L2 <= -1e299) return -1e300;
            best = min(best, min(L1, L2));
            if (L1 < L2) hi = m2; else lo = m1;
        }
        for (int i = lo; i <= hi; i++) {
            double L = evalL(grid[i]);
            if (L <= -1e299) return -1e300;
            best = min(best, L);
        }
        return (double)covCnt + max(0.0, best);
    }
    // ---- D_K: obligation-tier dual bound ------------------------------------
    // Packed candidates' own typed-degree obligations enter as
    // dualized rows  rho_v x_v - sum_{w in N_alive(v,A)} x_w <= 0  with
    // multipliers nu >= 0. For any (lambda, nu) >= 0 weak duality gives a
    // valid UB; we run a few subgradient rounds on the K rows of the packed
    // head and keep the minimum. Rows use ALIVE neighborhoods; when the ball
    // is complete, support vertices outside its cached span are irrelevant.
    // Capped balls are rejected below because their objective-variable domain
    // is incomplete even though obligation scans can add some supporters.
    double bound_dk() {
        if (!algo->bounding) return 1e300;   // defence in depth: b0Pools may be stale
        if (In.empty()) return 1e300;
        double beta = max(0.0, C.budget - (double)cIn);
        ensure_ball(beta);
        // D_K has the same complete-domain requirement as B2. Its obligation
        // rows can recover some outside supporters, but not every omitted score
        // variable, so a truncated ball must use the neutral fallback.
        if (ballTruncC) { dkSkippedOnTrunc++; return 1e300; }
        // variables: one per twin class in the ball (first member = rep)
        struct DV { double m, c, adj; int v, pool, extra; };
        static thread_local vector<DV> vars;
        static thread_local vector<int> clsPos, ctouch, poolId, ptouch;
        if ((int)clsPos.size() < max(nCls, 1)) clsPos.assign(max(nCls, 1), -1);
        if ((int)poolId.size() < G.n) poolId.assign(G.n, -1);
        vars.clear(); ctouch.clear(); ptouch.clear();
        for (size_t p = 0; p < b0Pools.size(); p++)
            for (int w : b0Pools[p]) { poolId[w] = (int)p; ptouch.push_back(w); }
        auto add_var = [&](int v) -> int {
            int cl = twinCls[v];
            if (clsPos[cl] >= 0) return clsPos[cl];
            clsPos[cl] = (int)vars.size(); ctouch.push_back(cl);
            vars.push_back({upperVal(v), G.cost[v], 0.0, v, poolId[v], 0});
            return clsPos[cl];
        };
        for (size_t i = ballLo; i < ballHi; i++) {
            int v = ballArena[i];
            if (!aliveNow[v] || inS[v]) continue;
            int j = add_var(v);
            // A pooled class's further members add covering
            // units at pure cost (twins share one coverage list) — without
            // them the pool row would demand n_A DISTINCT classes, cutting
            // optima that use twin siblings.
            if (vars[j].pool >= 0 && vars[j].v != v) vars[j].extra++;
        }
        int nBase = (int)vars.size();
        // inner solve at fixed (lambda, nu): greedy-exact (pools disjoint);
        // returns L and marks packed vars in 'sel'
        static thread_local vector<char> sel;
        static thread_local vector<double> prof;
        auto evalL = [&](double lam, bool record) -> double {
            if (record) sel.assign(vars.size(), 0);
            double L = lam * beta;
            static thread_local vector<pair<double,int>> pneg;
            // free vars
            for (size_t i = 0; i < vars.size(); i++) {
                if (vars[i].pool >= 0) continue;
                double r = vars[i].m + vars[i].adj - lam * vars[i].c;
                if (r > 0) { L += r; if (record) sel[i] = 1; }
            }
            // pool vars with forced fill
            for (size_t p = 0; p < b0Pools.size(); p++) {
                pneg.clear();
                double pos = 0; int npos = 0;
                for (size_t i = 0; i < vars.size(); i++) {
                    if (vars[i].pool != (int)p) continue;
                    double r = vars[i].m + vars[i].adj - lam * vars[i].c;
                    if (r > 0) { pos += r; npos++; if (record) sel[i] = 1; }
                    else pneg.push_back({r, (int)i});
                    for (int x = 0; x < vars[i].extra; x++)
                        pneg.push_back({-lam * vars[i].c, (int)i});
                }
                int need = b0Need[p] - npos;
                if (need > 0) {
                    if ((int)pneg.size() < need) return -1e300;
                    nth_element(pneg.begin(), pneg.begin() + (need - 1), pneg.end(),
                                greater<>());
                    for (int x = 0; x < need; x++) {
                        pos += pneg[x].first;
                        if (record) sel[pneg[x].second] = 1;
                    }
                }
                L += pos;
            }
            return L;
        };
        auto minimize = [&](bool record) -> double {
            static thread_local vector<double> grid;
            grid.clear(); grid.push_back(0.0);
            for (auto& g : vars)
                if (g.m + g.adj > 0) grid.push_back((g.m + g.adj) / g.c);
            sort(grid.begin(), grid.end());
            grid.erase(unique(grid.begin(), grid.end()), grid.end());
            int lo = 0, hi = (int)grid.size() - 1;
            double best = 1e300, bestLam = 0;
            while (hi - lo > 2) {
                int m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3;
                double L1 = evalL(grid[m1], false), L2 = evalL(grid[m2], false);
                if (L1 <= -1e299 || L2 <= -1e299) return -1e300;
                if (L1 < best) { best = L1; bestLam = grid[m1]; }
                if (L2 < best) { best = L2; bestLam = grid[m2]; }
                if (L1 < L2) hi = m2; else lo = m1;
            }
            for (int i = lo; i <= hi; i++) {
                double L = evalL(grid[i], false);
                if (L <= -1e299) return -1e300;
                if (L < best) { best = L; bestLam = grid[i]; }
            }
            if (record) evalL(bestLam, true);
            return best;
        };
        double bestL = minimize(true);
        // subgradient rounds on the packed head's obligation rows
        const int ROUNDS = 5, KROWS = 32;
        for (int r = 0; r < ROUNDS && bestL > -1e299; r++) {
            int added = 0;
            bool any = false;
            for (int i = 0; i < nBase && added < KROWS; i++) {
                if (!sel[i]) continue;
                int v = vars[i].v;
                auto& cs = C.consOf[G.type[v]];
                if (cs.empty()) continue;
                int base = 0; (void)base;
                for (size_t ci = 0; ci < cs.size(); ci++) {
                    // rho: v's residual demand against In (duplicate-type
                    // domination as in completion_analysis)
                    bool dominated = false;
                    for (size_t cj = 0; cj < cs.size(); cj++)
                        if (cj != ci && cs[cj].first == cs[ci].first &&
                            (cs[cj].second > cs[ci].second ||
                             (cs[cj].second == cs[ci].second && cj < ci)))
                            { dominated = true; break; }
                    if (dominated) continue;
                    int inCntV = 0, supSel = 0;
                    static thread_local vector<int> sups;
                    sups.clear();
                    for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                        int u = G.adj[e];
                        if (G.type[u] != cs[ci].first) continue;
                        if (inS[u]) { inCntV++; continue; }
                        if (!aliveNow[u]) continue;
                        sups.push_back(u);
                    }
                    int rho = cs[ci].second - inCntV;
                    if (rho <= 0) continue;
                    if ((int)sups.size() < rho) {           // v can never be packed
                        vars[i].adj = -1e18; any = true; continue;
                    }
                    for (int u : sups) {
                        int j = add_var(u);
                        if (sel.size() < vars.size()) sel.resize(vars.size(), 0);
                        if (sel[j]) supSel++;
                    }
                    if (supSel >= rho) continue;            // row satisfied
                    // subgradient step: dock v, credit supporters
                    double step = max(1e-3, (vars[i].m + vars[i].adj) /
                                             (2.0 * rho * (r + 1)));
                    vars[i].adj -= step * rho;
                    for (int u : sups) vars[clsPos[twinCls[u]]].adj += step;
                    any = true; added++;
                }
            }
            if (!any) break;
            double L = minimize(true);
            bestL = min(bestL, L);
        }
        for (int w : ptouch) poolId[w] = -1;
        for (int c0 : ctouch) clsPos[c0] = -1;
        if (bestL <= -1e299) return -1e300;
        return (double)covCnt + max(0.0, bestL);
    }
    // ---- search --------------------------------------------------------------
    // Deficit-first branching (verified against the MIMCS paper, Sec. V):
    //  * forced-supporter propagation to fixpoint: an open deficit whose
    //    eligible pool exactly equals its residual demand forces the pool in
    //    (Lemma "Forced Propagation"); budget overrun during forcing is fatal;
    //  * if a deficit remains open, branch ONLY over the eligible supporters
    //    of the deficit with the smallest pool (MRV): every feasible
    //    completion contains one of them, and the first-included-supporter
    //    order partitions the completions (Supporter Necessity lemma) — a far
    //    smaller branch set than the whole frontier;
    //  * otherwise branch by first-added candidate over the connected
    //    frontier. Both schemes use inline exclusions, so recursion depth
    //    stays bounded by |S|.
    void dfs() {                    // ball-frame wrapper
        size_t base = ballArena.size();
        size_t lo = ballLo, hi = ballHi;
        bool va = ballValid, tr = ballTruncC, so = ballSorted;
        ballValid = false;
        dfs_body();
        ballArena.resize(base);
        ballLo = lo; ballHi = hi; ballValid = va; ballTruncC = tr; ballSorted = so;
    }
    void dfs_body() {
        tick();
#ifdef PARANOID
        check_alive("dfs-entry");
#endif
        if (stop) { complete = false; record_trunc(); return; }
        // forced-supporter propagation (pool size == residual demand). The
        // pool size is O(1): eligible = aliveCnt - inCnt, demand = k - inCnt,
        // so pool == demand  <=>  aliveCnt == k.
        static thread_local vector<int> ws;
        vector<pair<int,size_t>> forced;             // (vertex, cover mark)
        bool dead = false;
        ll spins = 0;
        for (bool changed = algo->redForcedProp; changed && !dead; ) {
            if (++spins > 4 * (ll)G.n + 64) {        // fixpoint must terminate
                fprintf(stderr, "[BUG] forced-propagation spin: |In|=%zu cIn=%.4f "
                        "nUnsat=%d spins=%lld\n", In.size(), (double)cIn, nUnsat, spins);
                for (int v : In) {
                    auto& cs = C.consOf[G.type[v]]; int base = vcOff[v];
                    for (size_t i = 0; i < cs.size(); i++) {
                        int ta = 0, ti = 0;
                        for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                            int u = G.adj[e];
                            if (G.type[u] != cs[i].first) continue;
                            if (aliveNow[u]) ta++;
                            if (inS[u]) ti++;
                        }
                        fprintf(stderr, "  v=%d ty=%d cons(%d,%d) inCnt=%d aliveCnt=%d"
                                " trueAlive=%d trueIn=%d alive(v)=%d\n",
                                v, G.type[v], cs[i].first, cs[i].second,
                                inCnt[base + (int)i], aliveCnt[base + (int)i],
                                ta, ti, (int)aliveNow[v]);
                    }
                }
                abort();
            }
            changed = false;
            for (size_t qi = 0; qi < In.size() && !changed && !dead; qi++) {
                int v = In[qi];
                auto& cs = C.consOf[G.type[v]]; int base = vcOff[v];
                for (size_t i = 0; i < cs.size(); i++) {
                    if (inCnt[base + (int)i] >= cs[i].second) continue;
                    if (aliveCnt[base + (int)i] != cs[i].second) continue;
                    ws.clear();
                    for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                        int u = G.adj[e];
                        if (aliveNow[u] && !inS[u] && G.type[u] == cs[i].first)
                            ws.push_back(u);
                    }
                    for (int w : ws) {
                        if (!fits((double)cIn + G.cost[w])) { dead = true; break; }
                        size_t cm = covTrail.size();
                        include(w); forced.push_back({w, cm});
                        cntForcedInclusions++;
                    }
                    changed = true;
                    break;
                }
            }
        }
        double resNeed = 0, resCredit = 0, b0 = 1e300;
        if (!dead) {
            if (!In.empty() && nUnsat == 0 && covCnt > bestRaw &&
                (!requireConnIn || in_connected())) {
                bestRaw = covCnt; bestS = In; incumbentUpdates++;
            }
            // Connection lower bound for a multi-vertex forced query set.
            if (algo->bounding && requireConnIn && In.size() > 1 && !compBig && !in_connected()) {
                double lb = connect_lb();
                if (!fits((double)cIn + lb)) { dead = true; cntBoundPrunes++; }
            }
            // Completion, covering-knapsack, and obligation-tier bounds.
            if (!dead && algo->bounding && nUnsat > 0) {
                dead = !completion_analysis(resNeed, resCredit);
                if (dead) cntCompletionPrunes++;
                if (!dead) {
                    b0 = bound_covering();      // once per node
                    cntBoundCalls++;
                    if (b0 <= pruneThresh()) { dead = true; cntBoundPrunes++; }
                    else if (In.size() <= 2) {  // stubborn shallow node: D_K
                        double dk = bound_dk();
                        b0 = min(b0, dk);
                        if (b0 <= pruneThresh()) { dead = true; cntBoundPrunes++; }
                    }
                }
            }
        }
        if (!dead) {
            // ---- branch set ---------------------------------------------------
            vector<int> fr;
            if (algo->branchPriority && nUnsat > 0) {
                // MRV deficit branch: supporters of the tightest open deficit
                cntMrvNodes++;
                int bu = -1, bi = -1, bestPool = INT32_MAX;
                for (int v : In) {
                    auto& cs = C.consOf[G.type[v]]; int base = vcOff[v];
                    for (size_t i = 0; i < cs.size(); i++) {
                        if (inCnt[base + (int)i] >= cs[i].second) continue;
                        int p = aliveCnt[base + (int)i] - inCnt[base + (int)i];
                        if (p < bestPool) { bestPool = p; bu = v; bi = (int)i; }
                    }
                }
                int wantT = C.consOf[G.type[bu]][bi].first;
                for (int e = G.off[bu]; e < G.off[bu + 1]; e++) {
                    int u = G.adj[e];
                    if (aliveNow[u] && !inS[u] && G.type[u] == wantT) fr.push_back(u);
                }
            } else {
                st.fresh();
                for (int v : In)
                    for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                        int u = G.adj[e];
                        if (aliveNow[u] && !inS[u] && !st.test(u)) { st.set(u); fr.push_back(u); }
                    }
            }
            if (!fr.empty()) {
                if (algo->branchPriority) {
                    cntRankNodes++;
                    size_t evalK = min(fr.size(), (size_t)64);   // refine head by true marginal
                    partial_sort(fr.begin(), fr.begin() + evalK, fr.end(), [&](int a, int b) {
                        return (double)inf.cov1[a].size() / G.cost[a] >
                               (double)inf.cov1[b].size() / G.cost[b];
                    });
                    vector<pair<double,int>> head;
                    for (size_t i = 0; i < evalK; i++)
                        head.push_back({(margHot(fr[i]) + 1.0) / G.cost[fr[i]], fr[i]});
                    sort(head.begin(), head.end(), greater<>());
                    for (size_t i = 0; i < evalK; i++) fr[i] = head[i].second;
                } else {
                    // neutral order: v* = argmin_{v in F} id(v).  Same frontier
                    // candidate set F, no benefit/cost, deficit-aware or
                    // score-oriented ranking.
                    cntNeutralOrderNodes++;
                    sort(fr.begin(), fr.end());
                }

                const int BOUND_EVERY = compBig ? 1 : 4;
                size_t exMark = exTrail.size();
                double curUB = 1e300; int sinceB = 1 << 30;
                vector<int> doneCls;                 // twin classes already branched
                for (int w : fr) {
                    if (stop) {
                        complete = false;
                        record_trunc(resNeed, resCredit, b0); break;
                    }
                    if (!aliveNow[w]) continue;      // peeled by an earlier exclusion
                    if (algo->bounding) {
                        if (sinceB >= BOUND_EVERY) {
                            curUB = min(bound_now(resNeed, resCredit), b0); sinceB = 0;
                            cntBoundCalls++;
                        }
                        if (curUB <= pruneThresh()) { cntBoundPrunes++; break; }
                    }
                    // twin skip: completions taking w instead of an already-
                    // branched same-class sibling map (member swap) to equal-
                    // score completions inside that sibling's include-child
                    bool clsDone = false;
                    if (algo->redTwinSkip) {
                        for (int c0 : doneCls) if (c0 == twinCls[w]) { clsDone = true; break; }
                        if (!clsDone) doneCls.push_back(twinCls[w]);
                        else cntTwinBranchSkips++;
                    }
                    if (!clsDone && fits((double)cIn + G.cost[w])) {
                        size_t cm = covTrail.size();
                        include(w);
                        dfs();
                        undo_include(w, cm);
                    }
                    bool okc = exclude_cascade(w);
#ifdef PARANOID
                    check_alive("cascade-dfs");
#endif
                    if (!okc) break;                 // In vertex peeled: subtree dead
                    sinceB++;
                }
                undo_exclusions(exMark);
#ifdef PARANOID
                check_alive("undo-dfs");
#endif
            }
        }
        for (auto it = forced.rbegin(); it != forced.rend(); ++it)
            undo_include(it->first, it->second);
    }
    // Static per-component knapsack prefix.  Consumed ONLY by the Bounding
    // family (static_query, bound_now's boundary-crossing merge, record_trunc),
    // so it is not built when bounding is off.
    void build_static_items(const vector<int>& comp) {
        itemsV.clear();
        preCost.assign(1, 0); preVal.assign(1, 0);
        if (!algo->bounding) return;
        classSt.fresh();                 // one static item per twin class
        for (int v : comp) {
            if (inf.cov1[v].empty()) continue;
            if (algo->bndTwinDedup) {
                if (classSt.test(twinCls[v])) continue;
                classSt.set(twinCls[v]);
            }
            itemsV.push_back(v);
        }
        sort(itemsV.begin(), itemsV.end(), [&](int a, int b) {
            return (double)inf.cov1[a].size() / G.cost[a] >
                   (double)inf.cov1[b].size() / G.cost[b];
        });
        preCost.assign(itemsV.size() + 1, 0); preVal.assign(itemsV.size() + 1, 0);
        for (size_t i = 0; i < itemsV.size(); i++) {
            preCost[i + 1] = preCost[i] + G.cost[itemsV[i]];
            preVal[i + 1]  = preVal[i] + (double)inf.cov1[itemsV[i]].size();
        }
    }
    void run_comp(const vector<int>& comp) {
        // Component pre-prune with inexpensive root bounds.
        if (algo->bounding) {
            ll rough = min(ub_component(inf, comp),
                           ub_frac_knapsack(G, inf, comp, C.budget));
            if ((double)rough <= pruneThresh()) return;
        }
        curCompP = &comp;
        compBig = comp.size() > 3000;
        cminComp = 1e300;
        for (int v : comp) cminComp = min(cminComp, G.cost[v]);
        build_static_items(comp);
        vector<int> roots = comp;
        if (algo->branchPriority)        // [N3] root ordering by coverage density
            sort(roots.begin(), roots.end(), [&](int a, int b) {
                return (double)inf.cov1[a].size() / G.cost[a] >
                       (double)inf.cov1[b].size() / G.cost[b];
            });
        else
            sort(roots.begin(), roots.end());        // neutral: ascending id
        size_t exMark = exTrail.size();
        static thread_local vector<char> clsSeen;
        if ((int)clsSeen.size() < nCls) clsSeen.assign(max(nCls, 1), 0);
        vector<int> clsTouched;
        int ri = 0;
        for (int r : roots) {
            tick();
            if (stop) { complete = false; record_trunc(); break; }
            if (!aliveNow[r]) { ri++; continue; }
            // twin root: sets rooted at r map (member swap) to equal-score
            // sets already enumerated under the earlier same-class root.
            bool twinRootSkip = algo->redTwinSkip && clsSeen[twinCls[r]];
            if (twinRootSkip || !fits(G.cost[r])) {
                if (twinRootSkip) cntTwinBranchSkips++;
                exclude_cascade(r);
#ifdef PARANOID
                check_alive("root-skip");
#endif
                ri++; continue;
            }
            if (algo->redTwinSkip) {
                clsSeen[twinCls[r]] = 1; clsTouched.push_back(twinCls[r]);
            }
            if (algo->bounding && (ri++ & (compBig ? 63 : 3)) == 0 &&
                bound_now() <= pruneThresh()) { cntBoundPrunes++; break; }
            size_t cm = covTrail.size();
            include(r);
            dfs();
            undo_include(r, cm);
            exclude_cascade(r);       // sets containing r are fully enumerated
#ifdef PARANOID
            check_alive("root-cascade");
#endif
        }
        undo_exclusions(exMark);
        for (int c : clsTouched) clsSeen[c] = 0;
#ifdef PARANOID
        check_alive("root-undo");
#endif
    }
    void init_state(const vector<vector<int>>& comps) {
        t0 = chrono::steady_clock::now();
        ballTruncations = 0;
        coveringSkippedOnTrunc = dkSkippedOnTrunc = 0;
        cntCascadeRemovals = cntForcedInclusions = cntTwinBranchSkips = 0;
        cntBoundCalls = cntBoundPrunes = cntCompletionPrunes = 0;
        cntMrvNodes = cntRankNodes = cntNeutralOrderNodes = 0;
        b0Pools.clear(); b0Need.clear();
        int n = G.n;
        inS.assign(n, 0); In.clear(); cIn = 0; nUnsat = 0;
        vcOff.assign(n + 1, 0);
        for (int v = 0; v < n; v++)
            vcOff[v + 1] = vcOff[v] + (int)C.consOf[G.type[v]].size();
        inCnt.assign(max(vcOff[n], 1), 0);
        aliveCnt.assign(max(vcOff[n], 1), 0);
        cov.assign((size_t)max<ll>(inf.col1.R, 1), 0); covTrail.clear(); covCnt = 0;
        st.init(n);
        gst.init((size_t)max<ll>(inf.col1.R, 1));
        // tiering only pays once cold scans dominate: below 200k RR sets the
        // static-cold slack in tail items costs more pruning than the cheap
        // hot scans buy back (measured on DBLP), so the tier stays off
        if (Rhot <= 0)
            Rhot = (inf.col1.R <= 200000) ? inf.col1.R
                                          : max<ll>(inf.col1.R / 8, 100000);
        hotEnd.assign(n, 0);
        for (int v = 0; v < n; v++)
            hotEnd[v] = (int)(lower_bound(inf.cov1[v].begin(), inf.cov1[v].end(),
                                          (int)min<ll>(Rhot, (ll)INT32_MAX))
                              - inf.cov1[v].begin());
        aliveNow.assign(n, 0);
        for (auto& cm : comps) for (int v : cm) aliveNow[v] = 1;
        for (int v = 0; v < n; v++) if (aliveNow[v]) {
            auto& cs = C.consOf[G.type[v]]; int base = vcOff[v];
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e]; if (!aliveNow[u]) continue;
                for (size_t i = 0; i < cs.size(); i++)
                    if (cs[i].first == G.type[u]) aliveCnt[base + (int)i]++;
            }
        }
        // twin-class construction, general for arbitrary HIN schemas including
        // same-type relations (any multipartite structure). Two pairwise-
        // interchangeable kinds, both requiring equal type, cost and cov1:
        //   true twins   N[u] = N[v]   (adjacent, arises under <A,A,k>)
        //   false twins  N(u) = N(v)   (non-adjacent)
        // A mixed chain is impossible inside one class (members are pairwise
        // twins of one kind), so we group by closed neighborhoods first and
        // by open neighborhoods among the rest. For any class members w, w':
        // S -> S - w' + w preserves every vertex's typed degrees (w'' in S is
        // adjacent to both or neither), connectivity, cost and Score_R1.
        twinCls.assign(n, 0); nCls = 0;
        if (!algo->redTwinSkip && !algo->bndTwinDedup) {
            // No consumer of twin classes is enabled (Baseline-Enum): make every
            // vertex its own class.  Semantically identical to "no classes", and
            // it avoids charging the variant for a structure it never reads.
            for (int v = 0; v < n; v++) twinCls[v] = v;
            nCls = n;
        } else {
            vector<int> nb;
            auto core_nb = [&](int v, vector<int>& out, bool closed) {
                out.clear();
                for (int e = G.off[v]; e < G.off[v + 1]; e++)
                    if (aliveNow[G.adj[e]]) out.push_back(G.adj[e]);
                if (closed) {
                    out.insert(lower_bound(out.begin(), out.end(), v), v);
                }
            };
            vector<char> assigned(n, 0);
            for (int pass = 0; pass < 2; pass++) {
                bool closed = (pass == 0);
                map<tuple<int,double,size_t,size_t>, vector<int>> buck;
                for (int v = 0; v < n; v++) if (aliveNow[v] && !assigned[v]) {
                    core_nb(v, nb, closed);
                    buck[{G.type[v], G.cost[v], fnv_ints(nb), fnv_ints(inf.cov1[v])}]
                        .push_back(v);
                }
                for (auto& pr : buck) {
                    // exact-verify groups within each hash bucket
                    vector<vector<int>> groups; vector<vector<int>> gnb;
                    for (int v : pr.second) {
                        core_nb(v, nb, closed);
                        int f = -1;
                        for (size_t k = 0; k < groups.size(); k++)
                            if (gnb[k] == nb &&
                                inf.cov1[groups[k][0]] == inf.cov1[v]) { f = (int)k; break; }
                        if (f < 0) { groups.push_back({v}); gnb.push_back(nb); }
                        else groups[f].push_back(v);
                    }
                    for (auto& g : groups) {
                        if (closed && g.size() < 2) continue;   // retry as false twin
                        for (int v : g) { twinCls[v] = nCls; assigned[v] = 1; }
                        nCls++;
                    }
                }
            }
        }
        classSt.init(max(nCls, 1));
    }
    void run(const vector<vector<int>>& comps, const vector<int>& warm) {
        init_state(comps);
        if (!warm.empty()) {                       // warm start: speed only
            string why;
            if (verify_community(G, C, warm, C.budget, why)) {
                bestRaw = inf.covered(warm, 1); bestS = warm; incumbentUpdates++;
            }
        }
        vector<pair<ll,int>> order;                // most promising comps first
        for (size_t i = 0; i < comps.size(); i++)
            order.push_back({algo->bounding ? ub_component(inf, comps[i]) : 0, (int)i});
        if (algo->bounding) sort(order.begin(), order.end(), greater<>());
        for (auto& pr : order) {
            const auto& cm = comps[pr.second];
            if (stop) {
                complete = false;
                if (algo->bounding) {
                    ll rough = min(ub_component(inf, cm),
                                   ub_frac_knapsack(G, inf, cm, C.budget));
                    truncUB = max(truncUB, (double)rough);
                }
                continue;
            }
            run_comp(cm);
        }
    }
    // ---- query-anchored search (separate entry; global run() untouched) ------
    // Every solution must contain the query set Q: Q is force-included at the
    // root (no root loop / first-vertex partition needed), the search runs in
    // Q's component only, and with |Q| >= 2 incumbents additionally verify
    // In-connectivity since In may start disconnected.
    void run_query(const vector<vector<int>>& comps, const vector<int>& warm,
                   const vector<int>& Q) {
        init_state(comps);
        if (!warm.empty()) {                     // warm start must contain Q
            string why;
            bool hasQ = true;
            for (int q : Q)
                if (find(warm.begin(), warm.end(), q) == warm.end()) hasQ = false;
            if (hasQ && verify_community(G, C, warm, C.budget, why)) {
                bestRaw = inf.covered(warm, 1); bestS = warm; incumbentUpdates++;
            }
        }
        for (auto& cm : comps) {
            bool hasQ0 = false;
            for (int v : cm) if (v == Q[0]) { hasQ0 = true; break; }
            if (!hasQ0) continue;
            // per-component preamble (mirrors run_comp)
            curCompP = &cm;
            compBig = cm.size() > 3000;
            cminComp = 1e300;
            for (int v : cm) cminComp = min(cminComp, G.cost[v]);
            build_static_items(cm);
            // force the query set in and search the single anchored subtree
            requireConnIn = Q.size() > 1;
            bool ok = true;
            vector<pair<int,size_t>> qinc;
            for (int q : Q) {
                if (!aliveNow[q] || inS[q] || !fits((double)cIn + G.cost[q])) {
                    ok = false; break;
                }
                size_t cmk = covTrail.size();
                include(q); qinc.push_back({q, cmk});
            }
            if (ok) dfs();
            for (auto it = qinc.rbegin(); it != qinc.rend(); ++it)
                undo_include(it->first, it->second);
            requireConnIn = false;
            break;
        }
    }
    double certifiedUBraw() const {                // valid UB on OPT covered_1
        double b = (double)max<ll>(bestRaw, 0) * (1.0 + epsFrac);
        if (complete) return b;
        if (!algo->bounding) return 1e300;   // no in-search bound was computed
        return max(b, truncUB);
    }
    bool ubFromSearch() const { return complete || algo->bounding; }
};

// -------------------------------------------------------------- synthetic
static void synth(int n, int ntypes, double edge_p_scale, mt19937_64& rng,
                  HIN& G, Cfg& C, bool unitCost) {
    uniform_real_distribution<double> U(0, 1);
    vector<int> ty(n); vector<double> co(n);
    for (int i = 0; i < n; i++) {
        ty[i] = (int)(rng() % (ull)ntypes);
        co[i] = unitCost ? 1.0 : 0.5 + 2.5 * U(rng);
    }
    vector<pair<int,int>> es;
    double p = edge_p_scale * 3.0 / n;
    // same-type edges allowed at reduced rate: instances are general HINs
    // (arbitrary multipartite schema), not strictly cross-type
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if ((ty[i] != ty[j] || (rng() & 3) == 0) && U(rng) < p) es.push_back({i, j});
    // ensure some target-adjacent structure exists
    G.build(n, ntypes, ty, co, es);
    // constraints: 1-2 random typed pairs with k in {1,2}
    C = Cfg();
    int nc = 1 + (int)(rng() % 2);
    for (int c = 0; c < nc; c++) {
        int a = (int)(rng() % (ull)ntypes), b2 = (int)(rng() % (ull)ntypes);
        // reflexive constraints <A,A,k> kept half the time (general HINs)
        if (a == b2 && (rng() & 1)) b2 = (b2 + 1) % ntypes;
        C.cons.push_back({a, b2, 1 + (int)(rng() % 2)});
    }
    C.target_type = 0;
    C.gt_mode = (ntypes >= 2 && (rng() & 1)) ? "proj2" : "direct";
    C.gt_middle = 1 % ntypes;
    C.gamma_mode = (rng() & 1) ? "metapath" : "identity";
    if (C.gamma_mode == "metapath" && ntypes >= 2)
        C.gamma_paths.push_back({1 % ntypes, 0});
    { ull r3 = rng() % 3;
      C.ic_model = r3 == 0 ? "wc" : (r3 == 1 ? "const" : "wic"); }
    C.ic_p = 0.15;
    double tot = 0; for (double x : co) tot += x;
    C.budget = max(2.0, tot * (0.15 + 0.25 * U(rng)));
    C.rr1 = 400; C.rr2 = 400; C.delta = 0.1;
    C.ball_hops = 2; C.ball_cap = 200; C.minimize_passes = 2;
    C.finalize(ntypes);
}

// --------------------------------------------------------- brute max core
// exact maximum constraint-satisfying set for tiny n (union-closure check)
static vector<char> brute_core(const HIN& G, const Cfg& C) {
    int n = G.n;
    vector<char> best(n, 0);
    // union of all satisfying sets == max satisfying set; enumerate all masks
    for (unsigned mask = 0; mask < (1u << n); mask++) {
        // check satisfying
        bool okm = true;
        for (int v = 0; v < n && okm; v++) if (mask >> v & 1) {
            if (!C.inAS[G.type[v]]) { okm = false; break; }
            for (auto& pr : C.consOf[G.type[v]]) {
                int have = 0;
                for (int e = G.off[v]; e < G.off[v + 1]; e++)
                    if ((mask >> G.adj[e] & 1) && G.type[G.adj[e]] == pr.first) have++;
                if (have < pr.second) { okm = false; break; }
            }
        }
        if (okm) for (int v = 0; v < n; v++) if (mask >> v & 1) best[v] = 1;
    }
    return best;
}

// ------------------------------------------------------------------- modes
static int mode_selftest(int trials, ull seed, const AlgoCfg& algo) {
    mt19937_64 rng(seed);
    int c1p = 0, c1t = 0, c2p = 0, c2t = 0, c3p = 0, c3t = 0, c4p = 0, c4t = 0,
        c5p = 0, c5t = 0, c6p = 0, c6t = 0, c7p = 0, c7t = 0, c8p = 0, c8t = 0,
        c9p = 0, c9t = 0, c10p = 0, c10t = 0, c11p = 0, c11t = 0;
    for (int tr = 0; tr < trials; tr++) {
        int n = 8 + (int)(rng() % 19);          // 8..26
        int ntypes = 2 + (int)(rng() % 3);
        HIN G; Cfg C;
        synth(n, ntypes, 1.0 + (rng() % 3), rng, G, C, (rng() & 1));
        Influence inf; inf.init(G, C, rng);
        vector<char> member(G.n, 1), alive;
        peel_core(G, C, member, alive);
        // C1: core equals brute-force maximum satisfying set (n<=16)
        if (n <= 16) {
            c1t++;
            vector<char> bc = brute_core(G, C);
            if (bc == alive) c1p++;
            else fprintf(stderr, "[C1 FAIL] trial %d\n", tr);
        }
        vector<int> comp; vector<vector<int>> comps;
        components_of(G, alive, comp, comps);
        GadgetFinder gf(G, C, alive, inf);
        for (auto& cm : comps) for (int v : cm) gf.compute(v);
        // C2: gadget validity via independent verifier (no budget on gadgets;
        //     but family membership requires gamma<=b — checked separately)
        for (int v = 0; v < G.n; v++) if (gf.computed[v] && gf.ok[v]) {
            c2t++;
            string why;
            bool okv = verify_community(G, C, gf.K[v], 1e300, why) &&
                       binary_search(gf.K[v].begin(), gf.K[v].end(), v);
            if (okv) c2p++;
            else fprintf(stderr, "[C2 FAIL] trial %d v %d: %s\n", tr, v, why.c_str());
        }
        Brute B = brute_force(G, C, alive, comps, inf);
        SolveResult R = solve_lift(G, C, alive, comps, inf, gf);
        // C3: UB >= exact OPT on R1
        c3t++;
        double optScaled = (B.optRaw < 0) ? 0
            : (double)inf.nT * (double)B.optRaw / (double)max<ll>(C.rr1, 1);
        if (R.UB1_scaled + 1e-9 >= optScaled) c3p++;
        else fprintf(stderr, "[C3 FAIL] trial %d UB=%.4f OPT=%.4f\n", tr, R.UB1_scaled, optScaled);
        // C4: solver output verifies (when nonempty)
        if (!R.S.empty()) {
            c4t++;
            string why;
            if (verify_community(G, C, R.S, C.budget, why)) c4p++;
            else fprintf(stderr, "[C4 FAIL] trial %d: %s\n", tr, why.c_str());
        }
        // C5: solver <= OPT (only meaningful when brute force was complete)
        if (B.complete) {
            c5t++;
            if (R.score1 <= optScaled + 1e-9) c5p++;
            else fprintf(stderr, "[C5 FAIL] trial %d solver=%.4f OPT=%.4f\n", tr, R.score1, optScaled);
        }
        // C6: RR estimate vs forward MC on the returned set (4-sigma window)
        if (!R.S.empty() && inf.nT > 0) {
            c6t++;
            double se = 0;
            double mc = inf.forward_mc(G, C, R.S, 4000, rng, se);
            double seRR = (double)inf.nT / (2.0 * sqrt((double)C.rr2));
            if (fabs(mc - R.score2) <= 4.0 * (se + seRR) + 1e-9) c6p++;
            else fprintf(stderr, "[C6 FAIL] trial %d mc=%.3f rr=%.3f se=%.3f\n", tr, mc, R.score2, se);
        }
        // C7: certificate internal consistency
        c7t++;
        if (R.chat * (R.UB1_scaled + R.lam1) <= max(0.0, R.score2 - R.lam2) + 1e-9) c7p++;
        else { fprintf(stderr, "[C7 FAIL] trial %d\n", tr); }
        // C10: query-anchored exact equals query-restricted brute force
        {
            vector<int> coreV;
            for (int v = 0; v < G.n; v++) if (alive[v]) coreV.push_back(v);
            if (!coreV.empty()) {
                int q0 = coreV[rng() % coreV.size()];
                vector<int> Qs = {q0};
                if ((rng() & 1) && comps[comp[q0]].size() >= 2) {
                    auto& cq = comps[comp[q0]];
                    int q1 = cq[rng() % cq.size()];
                    if (q1 != q0) Qs.push_back(q1);
                }
                ll bq = -1;
                bool bqc = true;
                for (auto& cm : comps) {
                    bool has = false;
                    for (int v : cm) if (v == q0) { has = true; break; }
                    if (!has) continue;
                    int m = (int)cm.size();
                    if (m > 20) { bqc = false; break; }
                    for (unsigned mask = 1; mask < (1u << m); mask++) {
                        vector<int> S2; double c2 = 0; bool hasq = true;
                        for (int i = 0; i < m; i++) if (mask >> i & 1) {
                            S2.push_back(cm[i]); c2 += G.cost[cm[i]];
                        }
                        for (int qv : Qs)
                            if (find(S2.begin(), S2.end(), qv) == S2.end()) hasq = false;
                        if (!hasq || c2 > C.budget + 1e-9) continue;
                        string why;
                        if (!verify_community(G, C, S2, C.budget, why)) continue;
                        bq = max(bq, inf.covered(S2, 1));
                    }
                }
                if (bqc) {
                    ExactBnB exq(G, C, inf);
                    exq.nodeCap = 3'000'000; exq.timeCap = 5.0; exq.algo = &algo;
                    exq.run_query(comps, {}, Qs);
                    if (exq.complete) {
                        c10t++;
                        bool okS = true;
                        if (!exq.bestS.empty())
                            for (int qv : Qs)
                                if (find(exq.bestS.begin(), exq.bestS.end(), qv) ==
                                    exq.bestS.end()) okS = false;
                        if (exq.bestRaw == bq && okS) c10p++;
                        else fprintf(stderr, "[C10 FAIL] trial %d q=%d exact=%lld brute=%lld\n",
                                     tr, q0, exq.bestRaw, bq);
                    }
                }
            }
        }
        // C8: exact B&B (independent — no warm start) equals brute-force OPT;
        // C9: exact output passes the independent verifier
        {
            ExactBnB ex(G, C, inf);
            ex.nodeCap = 3'000'000; ex.timeCap = 5.0; ex.algo = &algo;
            ex.run(comps, {});
            if (ex.complete && B.complete) {
                c8t++;
                if (ex.bestRaw == B.optRaw) c8p++;
                else fprintf(stderr, "[C8 FAIL] trial %d exact=%lld brute=%lld\n",
                             tr, ex.bestRaw, B.optRaw);
            }
            if (!ex.bestS.empty()) {
                c9t++;
                string why;
                if (verify_community(G, C, ex.bestS, C.budget, why)) c9p++;
                else fprintf(stderr, "[C9 FAIL] trial %d: %s\n", tr, why.c_str());
            }
            // C11: force ball truncation on tiny brute-force-verifiable cases.
            // The advanced covering/D_K bounds must disable themselves, while
            // the compensated general bound preserves the exact optimum.
            if (B.complete) {
                ExactBnB excap(G, C, inf);
                excap.nodeCap = 3'000'000; excap.timeCap = 5.0; excap.algo = &algo;
                excap.exactBallCap = 5;
                excap.run(comps, {});
                if (excap.complete && excap.ballTruncations > 0) {
                    c11t++;
                    if (excap.bestRaw == B.optRaw) c11p++;
                    else fprintf(stderr, "[C11 FAIL] trial %d capped=%lld brute=%lld\n",
                                 tr, excap.bestRaw, B.optRaw);
                }
            }
        }
    }
    int P = c1p + c2p + c3p + c4p + c5p + c6p + c7p + c8p + c9p + c10p + c11p;
    int T = c1t + c2t + c3t + c4t + c5t + c6t + c7t + c8t + c9t + c10t + c11t;
    printf("selftest: algo=%s\n", algo.name);
    printf("selftest: C1 core-vs-brute      %d/%d\n", c1p, c1t);
    printf("selftest: C2 gadget-verifier    %d/%d\n", c2p, c2t);
    printf("selftest: C3 UB>=OPT            %d/%d\n", c3p, c3t);
    printf("selftest: C4 output-verifies    %d/%d\n", c4p, c4t);
    printf("selftest: C5 solver<=OPT        %d/%d\n", c5p, c5t);
    printf("selftest: C6 RR-vs-forwardMC    %d/%d\n", c6p, c6t);
    printf("selftest: C7 certificate        %d/%d\n", c7p, c7t);
    printf("selftest: C8 exact-vs-brute     %d/%d\n", c8p, c8t);
    printf("selftest: C9 exact-verifies     %d/%d\n", c9p, c9t);
    printf("selftest: C10 query-vs-brute    %d/%d\n", c10p, c10t);
    printf("selftest: C11 capped-ball exact %d/%d\n", c11p, c11t);
    printf("selftest: TOTAL                 %d/%d %s\n", P, T, (P == T ? "PASS" : "FAIL"));
    return (P == T) ? 0 : 1;
}

static int mode_demo(int n, ull seed) {
    mt19937_64 rng(seed);
    HIN G; Cfg C;
    synth(n, 3, 2.0, rng, G, C, false);
    C.rr1 = 20000; C.rr2 = 20000;
    C.finalize(G.ntypes);
    Influence inf; inf.init(G, C, rng);
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive, comp, comps);
    int coreN = 0; for (char a : alive) coreN += a;
    printf("demo: n=%d edges=%zu targets=%d core=%d comps=%zu budget=%.2f rr=%lld/%lld\n",
           G.n, G.adj.size() / 2, inf.nT, coreN, comps.size(), C.budget, C.rr1, C.rr2);
    GadgetFinder gf(G, C, alive, inf);
    SolveResult R = solve_lift(G, C, alive, comps, inf, gf);
    string why; bool okv = R.S.empty() ? false : verify_community(G, C, R.S, C.budget, why);
    printf("demo: source=%s |S|=%zu cost=%.2f/%.2f verified=%s\n",
           R.source.c_str(), R.S.size(), R.cost, C.budget, okv ? "yes" : why.c_str());
    printf("demo: Score_R1=%.2f Score_R2=%.2f\n", R.score1, R.score2);
    printf("demo: family: gadgets ok/tried=%d/%d sigma_c=%.2f theta=%.2f\n",
           R.gadgets_ok, R.gadgets_try, R.sigma_c, R.theta);
    printf("demo: UB1=%.2f lam1=%.2f lam2=%.2f  =>  c_hat=%.4f  (delta=%.2f)\n",
           R.UB1_scaled, R.lam1, R.lam2, R.chat, C.delta);
    return 0;
}

// ---- file loading -----------------------------------------------------------
static bool load_graph(const string& path, HIN& G) {
    ifstream f(path);
    if (!f) return false;
    int n, m, nt;
    if (!(f >> n >> m >> nt)) return false;
    vector<int> ty(n); vector<double> co(n);
    for (int i = 0; i < n; i++) f >> ty[i] >> co[i];
    vector<pair<int,int>> es(m);
    for (int i = 0; i < m; i++) f >> es[i].first >> es[i].second;
    G.build(n, nt, ty, co, es);
    return true;
}
static vector<int> parse_ints(const string& s) {
    vector<int> out; string cur;
    for (char ch : s + ",") {
        if (ch == ',' || ch == ' ') { if (!cur.empty()) out.push_back(stoi(cur)); cur.clear(); }
        else cur += ch;
    }
    return out;
}
static bool load_config(const string& path, Cfg& C) {
    ifstream f(path);
    if (!f) return false;
    string line;
    while (getline(f, line)) {
        size_t h = line.find('#'); if (h != string::npos) line = line.substr(0, h);
        istringstream ss(line);
        string key; if (!(ss >> key)) continue;
        // accept key=value too
        size_t eq = key.find('=');
        string val;
        if (eq != string::npos) { val = key.substr(eq + 1); key = key.substr(0, eq); }
        else { getline(ss, val); while (!val.empty() && val[0] == ' ') val.erase(0, 1); }
        if (key == "constraint") { auto v = parse_ints(val); if (v.size() == 3) C.cons.push_back({v[0], v[1], v[2]}); }
        else if (key == "AS") { C.AS = parse_ints(val); C.AS_explicit = true; }
        else if (key == "target_type") C.target_type = stoi(val);
        else if (key == "gamma_mode") C.gamma_mode = val;
        else if (key == "gamma_path") C.gamma_paths.push_back(parse_ints(val));
        else if (key == "gt_mode") C.gt_mode = val;
        else if (key == "gt_middle") C.gt_middle = stoi(val);
        else if (key == "gt_file") C.gt_file = val;
        else if (key == "ic_model") C.ic_model = val;
        else if (key == "ic_p") C.ic_p = stod(val);
        else if (key == "budget") C.budget = stod(val);
        else if (key == "rr1") C.rr1 = stoll(val);
        else if (key == "rr2") C.rr2 = stoll(val);
        else if (key == "delta") C.delta = stod(val);
        else if (key == "ball_hops") C.ball_hops = stoi(val);
        else if (key == "ball_cap") C.ball_cap = stoi(val);
        else if (key == "minimize_passes") C.minimize_passes = stoi(val);
    }
    return true;
}

static bool finalize_loaded_config(Cfg& C, int ntypes) {
    string err;
    if (C.finalize(ntypes, &err)) return true;
    fprintf(stderr, "config error: %s\n", err.c_str());
    return false;
}

static int mode_config(const string& gpath, const string& cpath) {
    HIN G; Cfg C;
    if (!load_graph(gpath, G)) { fprintf(stderr, "cannot read graph %s\n", gpath.c_str()); return 2; }
    if (!load_config(cpath, C)) { fprintf(stderr, "cannot read config %s\n", cpath.c_str()); return 2; }
    if (!finalize_loaded_config(C, G.ntypes)) return 2;
    C.print_effective(stdout);
    return 0;
}

static int mode_solve(const string& gpath, const string& cpath, ull seed) {
    HIN G; Cfg C;
    if (!load_graph(gpath, G)) { fprintf(stderr, "cannot read graph %s\n", gpath.c_str()); return 2; }
    if (!load_config(cpath, C)) { fprintf(stderr, "cannot read config %s\n", cpath.c_str()); return 2; }
    if (!finalize_loaded_config(C, G.ntypes)) return 2;
    mt19937_64 rng(seed);
    Influence inf; inf.init(G, C, rng);
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive, comp, comps);
    int coreN = 0; for (char a : alive) coreN += a;
    printf("solve: n=%d edges=%zu targets=%d core=%d comps=%zu\n",
           G.n, G.adj.size() / 2, inf.nT, coreN, comps.size());
    GadgetFinder gf(G, C, alive, inf);
    SolveResult R = solve_lift(G, C, alive, comps, inf, gf);
    string why; bool okv = R.S.empty() ? false : verify_community(G, C, R.S, C.budget, why);
    printf("solve: source=%s |S|=%zu cost=%.4f/%.4f verified=%s\n",
           R.source.c_str(), R.S.size(), R.cost, C.budget, okv ? "yes" : why.c_str());
    printf("solve: Score_R1=%.4f Score_R2=%.4f\n", R.score1, R.score2);
    printf("solve: family sigma_c=%.4f theta=%.4f (ok/tried=%d/%d)\n",
           R.sigma_c, R.theta, R.gadgets_ok, R.gadgets_try);
    printf("solve: certificate c_hat=%.6f  [UB1=%.4f lam1=%.4f lam2=%.4f delta=%.3f]\n",
           R.chat, R.UB1_scaled, R.lam1, R.lam2, C.delta);
    printf("solve: community:");
    for (int v : R.S) printf(" %d", v);
    printf("\n");
    return 0;
}

// ---- exact vs approximate on a loaded instance ------------------------------
static int mode_exact(const AlgoCfg& algo, const string& gpath, const string& cpath, ull seed,
                      double budgetOv, ll nodeCap, double timeCap,
                      double epsFrac = 0.0, double kernelB = 0.0) {
    HIN G; Cfg C;
    if (!load_graph(gpath, G)) { fprintf(stderr, "cannot read graph %s\n", gpath.c_str()); return 2; }
    if (!load_config(cpath, C)) { fprintf(stderr, "cannot read config %s\n", cpath.c_str()); return 2; }
    if (budgetOv > 0) C.budget = budgetOv;
    if (!finalize_loaded_config(C, G.ntypes)) return 2;
    mt19937_64 rng(seed);
    Influence inf; inf.init(G, C, rng);
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive, comp, comps);
    int coreN = 0; for (char a : alive) coreN += a;
    printf("exact: n=%d edges=%zu targets=%d core=%d comps=%zu budget=%.4f\n",
           G.n, G.adj.size() / 2, inf.nT, coreN, comps.size(), C.budget);
    auto tL = chrono::steady_clock::now();
    GadgetFinder gf(G, C, alive, inf);
    SolveResult R = solve_lift(G, C, alive, comps, inf, gf);
    double liftT = secs_since(tL);
    printf("exact: lift   Score_R1=%.4f cost=%.4f |S|=%zu time=%.2fs\n",
           R.score1, R.cost, R.S.size(), liftT);
    if (kernelB > 0) {                 // hybrid warm start: exact kernel + extension
        double fullB = C.budget;
        C.budget = kernelB;
        SolveResult Rk = solve_lift(G, C, alive, comps, inf, gf);
        ExactBnB exk(G, C, inf);
        exk.nodeCap = nodeCap; exk.timeCap = min(timeCap * 0.3, 300.0);
        exk.algo = &algo;
        exk.run(comps, Rk.S);
        C.budget = fullB;
        if (!exk.bestS.empty()) {
            SolveResult Rh = solve_lift(G, C, alive, comps, inf, gf, &exk.bestS);
            if (Rh.score1 > R.score1) R = Rh;
            printf("exact: warm   Score_R1=%.4f (hybrid kernel=%.1f, kernel %s)\n",
                   R.score1, kernelB, exk.complete ? "proven" : "anytime");
        }
    }
    ExactBnB ex(G, C, inf);
    ex.nodeCap = nodeCap; ex.timeCap = timeCap;
    ex.epsFrac = epsFrac;
    ex.algo = &algo;
    printf("exact: algo=%s\n", algo.name);
    auto tE = chrono::steady_clock::now();
    ex.run(comps, R.S);
    double exT = secs_since(tE);
    double scale = (double)inf.nT / (double)max<ll>(C.rr1, 1);
    double exSc = (ex.bestRaw < 0) ? 0 : scale * (double)ex.bestRaw;
    double exUB = scale * ex.certifiedUBraw();
    string why; bool okv = ex.bestS.empty() ? false
                                            : verify_community(G, C, ex.bestS, C.budget, why);
    printf("exact: best   Score_R1=%.4f cost=%.4f |S|=%zu verified=%s complete=%s nodes=%lld time=%.2fs\n",
           exSc, GadgetFinder::cost_of(G, ex.bestS), ex.bestS.size(),
           okv ? "yes" : (ex.bestS.empty() ? "n/a" : why.c_str()),
           ex.complete ? "yes" : "no", ex.nodes, exT);
    printf("exact: incumbent_updates=%lld\n", ex.incumbentUpdates);
    printf("exact: ball_truncations=%lld covering_skipped_trunc=%lld dk_skipped_trunc=%lld\n",
           ex.ballTruncations, ex.coveringSkippedOnTrunc, ex.dkSkippedOnTrunc);
    printf("exact: community:");
    for (int v : ex.bestS) printf(" %d", v);
    printf("\n");
    printf("exact: certified UB_R1=%.4f  opt-gap<=%.2f%%%s\n",
           exUB, exSc > 0 ? 100.0 * (exUB - exSc) / exSc : 0.0,
           epsFrac > 0 ? "  (eps-certified)" : "");
    printf("exact: approx-ratio lift/exact=%.4f  certified lift/UB>=%.4f\n",
           exSc > 0 ? R.score1 / exSc : 0.0, exUB > 0 ? R.score1 / exUB : 0.0);
    // exact UB strengthens the a-posteriori certificate: c_hat uses min(UBs)
    double sc2 = ex.bestS.empty() ? 0 : inf.score(ex.bestS, 2);
    double ubCert = min(R.UB1_scaled, exUB);
    double chat = max(0.0, sc2 - R.lam2) / (ubCert + R.lam1);
    printf("exact: strengthened c_hat=%.6f  [minUB=%.4f lam1=%.4f lam2=%.4f]\n",
           chat, ubCert, R.lam1, R.lam2);
    return 0;
}

// ---- exact vs approximate (vs brute when tiny) on a synthetic instance ------
static int mode_compare(int n, ull seed, double budgetOv, ll nodeCap, double timeCap) {
    mt19937_64 rng(seed);
    HIN G; Cfg C;
    synth(n, 3, 2.0, rng, G, C, false);
    C.rr1 = C.rr2 = 4000;
    if (budgetOv > 0) C.budget = budgetOv;
    C.finalize(G.ntypes);
    Influence inf; inf.init(G, C, rng);
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive, comp, comps);
    int coreN = 0; for (char a : alive) coreN += a;
    size_t mx = 0; for (auto& cm : comps) mx = max(mx, cm.size());
    printf("compare: n=%d edges=%zu targets=%d core=%d comps=%zu maxcomp=%zu budget=%.2f\n",
           G.n, G.adj.size() / 2, inf.nT, coreN, comps.size(), mx, C.budget);
    auto tL = chrono::steady_clock::now();
    GadgetFinder gf(G, C, alive, inf);
    SolveResult R = solve_lift(G, C, alive, comps, inf, gf);
    double liftT = secs_since(tL);
    printf("compare: lift  Score_R1=%.4f cost=%.4f/%.2f |S|=%zu time=%.3fs\n",
           R.score1, R.cost, C.budget, R.S.size(), liftT);
    ExactBnB ex(G, C, inf);
    ex.nodeCap = nodeCap; ex.timeCap = timeCap;
    auto tE = chrono::steady_clock::now();
    ex.run(comps, R.S);
    double exT = secs_since(tE);
    double scale = (double)inf.nT / (double)max<ll>(C.rr1, 1);
    double exSc = (ex.bestRaw < 0) ? 0 : scale * (double)ex.bestRaw;
    double exUB = scale * ex.certifiedUBraw();
    string why; bool okv = ex.bestS.empty() ? false
                                            : verify_community(G, C, ex.bestS, C.budget, why);
    printf("compare: exact Score_R1=%.4f cost=%.4f |S|=%zu verified=%s complete=%s nodes=%lld time=%.3fs UB=%.4f\n",
           exSc, GadgetFinder::cost_of(G, ex.bestS), ex.bestS.size(),
           okv ? "yes" : (ex.bestS.empty() ? "n/a" : why.c_str()),
           ex.complete ? "yes" : "no", ex.nodes, exT, exUB);
    printf("compare: ball_truncations=%lld covering_skipped_trunc=%lld dk_skipped_trunc=%lld\n",
           ex.ballTruncations, ex.coveringSkippedOnTrunc, ex.dkSkippedOnTrunc);
    if (mx <= 20) {                       // brute feasible: triple agreement
        Brute B = brute_force(G, C, alive, comps, inf);
        double brSc = (B.optRaw < 0) ? 0 : scale * (double)B.optRaw;
        printf("compare: brute Score_R1=%.4f agree=%s\n",
               brSc, (B.complete && ex.complete && B.optRaw == ex.bestRaw) ? "yes" : "NO");
    }
    printf("compare: approx-ratio lift/exact=%.4f%s certified lift/UB>=%.4f\n",
           exSc > 0 ? R.score1 / exSc : 0.0, ex.complete ? " (exact OPT)" : " (incumbent)",
           exUB > 0 ? R.score1 / exUB : 0.0);
    return 0;
}

// ---- kernel-exact + greedy-extension hybrid ---------------------------------
// Solve a small kernel budget exactly (B&B, anytime), then grow the kernel to
// the full budget with the closure-greedy lift. Exact where exact is strong
// (deep combinatorial choices at small budgets), greedy where the space is
// hopeless for search.
static int mode_hybrid(const string& gpath, const string& cpath, ull seed,
                       double budgetOv, double kernelB, ll nodeCap, double timeCap) {
    HIN G; Cfg C;
    if (!load_graph(gpath, G)) { fprintf(stderr, "cannot read graph %s\n", gpath.c_str()); return 2; }
    if (!load_config(cpath, C)) { fprintf(stderr, "cannot read config %s\n", cpath.c_str()); return 2; }
    if (budgetOv > 0) C.budget = budgetOv;
    if (!finalize_loaded_config(C, G.ntypes)) return 2;
    mt19937_64 rng(seed);
    Influence inf; inf.init(G, C, rng);
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive, comp, comps);
    double fullB = C.budget;
    if (kernelB <= 0) kernelB = min(fullB, 6.0);
    printf("hybrid: n=%d targets=%d budget=%.4f kernel=%.4f\n",
           G.n, inf.nT, fullB, kernelB);
    GadgetFinder gf(G, C, alive, inf);
    // baseline: plain lift at the full budget
    SolveResult Rb = solve_lift(G, C, alive, comps, inf, gf);
    printf("hybrid: lift-baseline Score_R1=%.4f Score_R2=%.4f cost=%.4f |S|=%zu\n",
           Rb.score1, Rb.score2, Rb.cost, Rb.S.size());
    // kernel: exact at the kernel budget (warm-started by lift at that budget)
    C.budget = kernelB;
    SolveResult Rk = solve_lift(G, C, alive, comps, inf, gf);
    ExactBnB ex(G, C, inf);
    ex.nodeCap = nodeCap; ex.timeCap = timeCap;
    auto tE = chrono::steady_clock::now();
    ex.run(comps, Rk.S);
    double scale = (double)inf.nT / (double)max<ll>(C.rr1, 1);
    printf("hybrid: kernel-exact Score_R1=%.4f |S|=%zu complete=%s nodes=%lld time=%.2fs\n",
           ex.bestRaw < 0 ? 0.0 : scale * (double)ex.bestRaw, ex.bestS.size(),
           ex.complete ? "yes" : "no", ex.nodes, secs_since(tE));
    printf("hybrid: ball_truncations=%lld covering_skipped_trunc=%lld dk_skipped_trunc=%lld\n",
           ex.ballTruncations, ex.coveringSkippedOnTrunc, ex.dkSkippedOnTrunc);
    // extension: closure-greedy growth of the kernel to the full budget
    C.budget = fullB;
    SolveResult Rh = ex.bestS.empty()
        ? Rb : solve_lift(G, C, alive, comps, inf, gf, &ex.bestS);
    string why;
    bool okv = Rh.S.empty() ? false : verify_community(G, C, Rh.S, C.budget, why);
    printf("hybrid: result Score_R1=%.4f Score_R2=%.4f cost=%.4f/%.4f |S|=%zu verified=%s source=%s\n",
           Rh.score1, Rh.score2, Rh.cost, fullB, Rh.S.size(),
           okv ? "yes" : why.c_str(), Rh.source.c_str());
    printf("hybrid: improvement over lift = %+.2f%%  (R2: %+.2f%%)\n",
           Rb.score1 > 0 ? 100.0 * (Rh.score1 - Rb.score1) / Rb.score1 : 0.0,
           Rb.score2 > 0 ? 100.0 * (Rh.score2 - Rb.score2) / Rb.score2 : 0.0);
    printf("hybrid: certificate c_hat=%.6f (lift %.6f) [UB1=%.4f lam1=%.4f]\n",
           Rh.chat, Rb.chat, Rh.UB1_scaled, Rh.lam1);
    return 0;
}

// ---- query-anchored community search ----------------------------------------
// Find the most influential feasible community CONTAINING the query vertices.
// Preprocessing: any solution lies within the budget-bounded hop ball of the
// query set, so the core is restricted to ball+peel before the search.
static int mode_query(const string& gpath, const string& cpath, ull seed,
                      const vector<int>& Q, double budgetOv, double epsFrac,
                      ll nodeCap, double timeCap) {
    HIN G; Cfg C;
    if (!load_graph(gpath, G)) { fprintf(stderr, "cannot read graph %s\n", gpath.c_str()); return 2; }
    if (!load_config(cpath, C)) { fprintf(stderr, "cannot read config %s\n", cpath.c_str()); return 2; }
    if (budgetOv > 0) C.budget = budgetOv;
    if (!finalize_loaded_config(C, G.ntypes)) return 2;
    if (Q.empty()) { fprintf(stderr, "query: need --q v1,v2,...\n"); return 2; }
    for (int q : Q) if (q < 0 || q >= G.n) { fprintf(stderr, "query: bad vertex %d\n", q); return 2; }
    mt19937_64 rng(seed);
    Influence inf; inf.init(G, C, rng);
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    for (int q : Q) if (!alive[q]) {
        printf("query: INFEASIBLE — vertex %d not in the relational core\n", q);
        return 0;
    }
    // anchored reduction (query-driven pruning): a member v of any solution
    // satisfies c(Q) + cheapest-interior-path(Q -> v) + c(v) <= b; vertex-
    // weighted Dijkstra beats the hop ball wherever costs vary. Iterated
    // with the peel to a fixpoint (each pass is individually sound).
    double cQ = 0;
    for (int q : Q) cQ += G.cost[q];
    vector<char> alive2 = alive;
    vector<char> isQ(G.n, 0);
    for (int q : Q) isQ[q] = 1;
    for (int pass = 0; pass < 5; pass++) {
        vector<double> dist(G.n, 1e300);
        priority_queue<pair<double,int>, vector<pair<double,int>>,
                       greater<pair<double,int>>> pq;
        for (int q : Q) { dist[q] = 0; pq.push({0, q}); }
        while (!pq.empty()) {
            auto pr2 = pq.top(); pq.pop();
            double d = pr2.first; int v = pr2.second;
            if (d > dist[v]) continue;
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e];
                if (!alive2[u]) continue;
                double nd = d + (isQ[v] ? 0.0 : G.cost[v]);
                if (nd < dist[u] - 1e-12) { dist[u] = nd; pq.push({nd, u}); }
            }
        }
        vector<char> keep(G.n, 0);
        int removed = 0;
        for (int v = 0; v < G.n; v++) {
            if (!alive2[v]) continue;
            if (isQ[v] || cQ + dist[v] + G.cost[v] <= C.budget + 1e-9) keep[v] = 1;
            else removed++;
        }
        int c0 = 0; for (int v = 0; v < G.n; v++) c0 += alive2[v];
        vector<char> next;
        peel_core(G, C, keep, next);
        int c1 = 0; for (int v = 0; v < G.n; v++) c1 += next[v];
        alive2 = next;
        if (removed == 0 && c1 == c0) break;
    }
    for (int q : Q) if (!alive2[q]) {
        printf("query: INFEASIBLE — query cannot be supported within budget %.2f\n", C.budget);
        return 0;
    }
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive2, comp, comps);
    if (Q.size() > 1)
        for (size_t i = 1; i < Q.size(); i++)
            if (comp[Q[i]] != comp[Q[0]]) {
                printf("query: INFEASIBLE — query vertices in different components\n");
                return 0;
            }
    int core2 = 0; for (char a : alive2) core2 += a;
    printf("query: |Q|=%zu budget=%.2f anchored-core=%d\n",
           Q.size(), C.budget, core2);
    // warm start: greedy growth seeded by Q (result contains Q by construction)
    GadgetFinder gf(G, C, alive2, inf);
    SolveResult Rw = solve_lift(G, C, alive2, comps, inf, gf, &Q);
    bool warmOk = false;
    {
        string why;
        warmOk = !Rw.S.empty() && verify_community(G, C, Rw.S, C.budget, why);
        for (int q : Q)
            if (find(Rw.S.begin(), Rw.S.end(), q) == Rw.S.end()) warmOk = false;
    }
    printf("query: seeded-greedy Score_R1=%.4f |S|=%zu %s\n",
           Rw.score1, Rw.S.size(), warmOk ? "(warm start)" : "(unusable)");
    ExactBnB ex(G, C, inf);
    ex.nodeCap = nodeCap; ex.timeCap = timeCap; ex.epsFrac = epsFrac;
    auto tE = chrono::steady_clock::now();
    ex.run_query(comps, warmOk ? Rw.S : vector<int>{}, Q);
    double scale = (double)inf.nT / (double)max<ll>(C.rr1, 1);
    double sc = ex.bestRaw < 0 ? 0 : scale * (double)ex.bestRaw;
    double ub = scale * ex.certifiedUBraw();
    // the root-level knapsack UB is often tighter than truncation records
    {
        ll rough = 0;
        for (auto& cm2 : comps)
            rough = max(rough, min(ub_component(inf, cm2),
                                   ub_frac_knapsack(G, inf, cm2, C.budget)));
        ub = min(ub, scale * (double)rough);
        ub = max(ub, sc);
    }
    string why; bool okv = ex.bestS.empty() ? false
                                            : verify_community(G, C, ex.bestS, C.budget, why);
    printf("query: best Score_R1=%.4f cost=%.4f |S|=%zu verified=%s complete=%s nodes=%lld time=%.2fs\n",
           sc, GadgetFinder::cost_of(G, ex.bestS), ex.bestS.size(),
           okv ? "yes" : (ex.bestS.empty() ? "none-found" : why.c_str()),
           ex.complete ? "yes" : "no", ex.nodes, secs_since(tE));
    printf("query: ball_truncations=%lld covering_skipped_trunc=%lld dk_skipped_trunc=%lld\n",
           ex.ballTruncations, ex.coveringSkippedOnTrunc, ex.dkSkippedOnTrunc);
    printf("query: certified UB=%.4f gap<=%.2f%%%s\n", ub,
           sc > 0 ? 100.0 * (ub - sc) / sc : 0.0,
           epsFrac > 0 ? " (eps-certified)" : "");
    printf("query: community:");
    for (int v : ex.bestS) printf(" %d", v);
    printf("\n");
    return 0;
}

// ---- single-query exact mode (target-type restricted) ------------------------
// Exact search of the query-conditioned space
//   F(q) = { S : q in S, S connected, cost(S) <= b, S satisfies constraints }
// for a SINGLE query vertex q with type(q) == target_type. Thin wrapper over
// the query-anchored machinery (peel + anchored reduction + Q-seeded warm
// start + ExactBnB::run_query); adds the type restriction, an explicit status
// taxonomy, and a machine-parsable final result block. Existing modes are
// untouched. query_exact=yes refers to the QUERY-CONDITIONED optimum only,
// never to the global no-query optimum.
static int mode_query_exact(const string& gpath, const string& cpath, ull seed,
                            const string& qArg, double budgetOv, double epsFrac,
                            ll nodeCap, double timeCap, const AlgoCfg& algo) {
    HIN G; Cfg C;
    if (!load_graph(gpath, G)) { fprintf(stderr, "cannot read graph %s\n", gpath.c_str()); return 2; }
    if (!load_config(cpath, C)) { fprintf(stderr, "cannot read config %s\n", cpath.c_str()); return 2; }
    if (budgetOv > 0) C.budget = budgetOv;
    if (!finalize_loaded_config(C, G.ntypes)) return 2;
    if (qArg.empty() || qArg.find(',') != string::npos) {   // single query only
        fprintf(stderr, "query_exact: need a single --query <vertex-id>\n");
        return 2;
    }
    int q = -1;
    try { q = stoi(qArg); } catch (...) { q = -1; }
    if (q < 0 || q >= G.n) {
        fprintf(stderr, "query_exact: bad vertex id '%s'\n", qArg.c_str());
        return 2;
    }
    // ---- result fields, printed once by finish() ----------------------------
    string preStatus = "OK", stopReason = "";
    bool queryExact = false, feasible = false, timedOut = false, hitNodeCap = false;
    bool warmOk = false; double warmScore = 0, warmCost = 0; size_t warmSize = 0;
    double bestScore = 0, bestCost = 0, ub = 0, initScore = 0;
    ll visNodes = 0, incUpd = 0;
    ll ballTrunc = 0, coverSkipTrunc = 0, dkSkipTrunc = 0;
    int compId = -1, compSize = 0, qDeg = 0;
    // Variant observability
    int anchorPasses = 0; ll anchorRemoved = 0;
    bool ubFromSearch = true;
    ll cCascade = 0, cForced = 0, cTwinSkip = 0, cBndCalls = 0, cBndPrunes = 0,
       cComplPrunes = 0, cMrvNodes = 0, cRankNodes = 0, cNeutralNodes = 0;
    vector<int> bestS;
    auto t0 = chrono::steady_clock::now();
    auto finish = [&]() -> int {
        printf("query_exact: algo=%s reduction_beyond_r1=%s bounding=%s "
               "branching_priority=%s r1_peel=on rr_accel=on warm_start=on "
               "node_cap=not_used eps=%.4f\n",
               algo.name,
               onoff(algo.redAnchor || algo.redCascade || algo.redForcedProp ||
                     algo.redTwinSkip),
               onoff(algo.bounding), onoff(algo.branchPriority), epsFrac);
        printf("query_exact: algo_switches r2_anchor=%s r3_cascade=%s "
               "r4_forced_prop=%s r5a_twin_skip=%s b12_twin_dedup=%s\n",
               onoff(algo.redAnchor), onoff(algo.redCascade),
               onoff(algo.redForcedProp), onoff(algo.redTwinSkip),
               onoff(algo.bndTwinDedup));
        printf("query_exact: mode=query_exact dataset=%s\n", gpath.c_str());
        printf("query_exact: config=%s\n", cpath.c_str());
        printf("query_exact: budget=%.4f seed=%llu\n", C.budget, (unsigned long long)seed);
        printf("query_exact: query_id=%d query_type=%d target_type=%d query_cost=%.6f\n",
               q, G.type[q], C.target_type, G.cost[q]);
        printf("query_exact: query_component_id=%d query_component_size=%d query_degree=%d\n",
               compId, compSize, qDeg);
        printf("query_exact: query_initial_score=%.4f\n", initScore);
        printf("query_exact: query_preprocessing_status=%s\n", preStatus.c_str());
        printf("query_exact: warm_start_success=%s warm_start_score=%.4f "
               "warm_start_size=%zu warm_start_cost=%.4f\n",
               warmOk ? "yes" : "no", warmScore, warmSize, warmCost);
        printf("query_exact: query_exact=%s feasible_found=%s timeout=%s node_cap=%s\n",
               queryExact ? "yes" : "no", feasible ? "yes" : "no",
               timedOut ? "yes" : "no", hitNodeCap ? "yes" : "no");
        printf("query_exact: stop_reason=%s\n", stopReason.c_str());
        vector<int> tc(G.ntypes, 0);
        for (int v : bestS) tc[G.type[v]]++;
        printf("query_exact: best_score=%.4f best_size=%zu best_cost=%.4f "
               "best_type_distribution=", bestScore, bestS.size(), bestCost);
        for (int t = 0; t < G.ntypes; t++) printf("%s%d:%d", t ? "," : "", t, tc[t]);
        printf("\n");
        printf("query_exact: certified_UB=%.4f gap<=%.2f%%\n", ub,
               bestScore > 0 ? 100.0 * (ub - bestScore) / bestScore : 0.0);
        printf("query_exact: runtime=%.2fs visited_nodes=%lld incumbent_updates=%lld\n",
               secs_since(t0), visNodes, incUpd);
        printf("query_exact: ball_truncations=%lld covering_skipped_trunc=%lld "
               "dk_skipped_trunc=%lld\n", ballTrunc, coverSkipTrunc, dkSkipTrunc);
        printf("query_exact: ub_source=%s\n", ubFromSearch ? "search" : "root");
        printf("query_exact: abl_anchor_passes=%d abl_anchor_removed=%lld "
               "abl_cascade_removals=%lld abl_forced_inclusions=%lld "
               "abl_twin_skips=%lld abl_bound_calls=%lld abl_bound_prunes=%lld "
               "abl_completion_prunes=%lld abl_mrv_nodes=%lld "
               "abl_rank_nodes=%lld abl_neutral_order_nodes=%lld\n",
               anchorPasses, anchorRemoved, cCascade, cForced, cTwinSkip,
               cBndCalls, cBndPrunes, cComplPrunes, cMrvNodes, cRankNodes,
               cNeutralNodes);
        printf("query_exact: best_node_list=");
        for (int v : bestS) printf(" %d", v);
        printf("\n");
        return 0;
    };
    // (1) type restriction: only target-type query nodes are accepted
    if (G.type[q] != C.target_type) {
        preStatus = stopReason = "INVALID_QUERY_TYPE";
        return finish();
    }
    // (2) cost(q) > b is already an exact proof that F(q) is empty
    if (G.cost[q] > C.budget + 1e-9 + 1e-12 * fabs(C.budget)) {
        preStatus = stopReason = "STATIC_QUERY_INFEASIBLE_COST";
        queryExact = true;
        return finish();
    }
    mt19937_64 rng(seed);
    Influence inf; inf.init(G, C, rng);
    initScore = inf.score({q}, 1);
    // (3) q must survive the static relational-core peel [Fact 1.1]
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    if (!alive[q]) {
        preStatus = stopReason = "STATIC_QUERY_NOT_IN_CANDIDATE_COMPONENT";
        queryExact = true;
        return finish();
    }
    // (4) anchored reduction, identical to mode_query with |Q|=1: any member v
    //     of a solution satisfies c(q) + interior-path(q->v) + c(v) <= b;
    //     Dijkstra filter iterated with the peel to a fixpoint. q is exempt
    //     from the filter; if the fixpoint removes q, F(q) is proven empty.
    // This reduction is disabled in baseline_enum, which keeps the relational
    // core unchanged before enumeration.
    vector<int> Q = {q};
    double cQ = G.cost[q];
    vector<char> alive2 = alive;
    vector<char> isQ(G.n, 0);
    isQ[q] = 1;
    for (int pass = 0; algo.redAnchor && pass < 5; pass++) {
        anchorPasses++;
        vector<double> dist(G.n, 1e300);
        priority_queue<pair<double,int>, vector<pair<double,int>>,
                       greater<pair<double,int>>> pq;
        dist[q] = 0; pq.push({0, q});
        while (!pq.empty()) {
            auto pr2 = pq.top(); pq.pop();
            double d = pr2.first; int v = pr2.second;
            if (d > dist[v]) continue;
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e];
                if (!alive2[u]) continue;
                double nd = d + (isQ[v] ? 0.0 : G.cost[v]);
                if (nd < dist[u] - 1e-12) { dist[u] = nd; pq.push({nd, u}); }
            }
        }
        vector<char> keep(G.n, 0);
        int removed = 0;
        for (int v = 0; v < G.n; v++) {
            if (!alive2[v]) continue;
            if (isQ[v] || cQ + dist[v] + G.cost[v] <= C.budget + 1e-9) keep[v] = 1;
            else removed++;
        }
        int c0 = 0; for (int v = 0; v < G.n; v++) c0 += alive2[v];
        vector<char> nextAlive;
        peel_core(G, C, keep, nextAlive);
        int c1 = 0; for (int v = 0; v < G.n; v++) c1 += nextAlive[v];
        anchorRemoved += (ll)(c0 - c1);
        alive2 = nextAlive;
        if (removed == 0 && c1 == c0) break;
    }
    if (!alive2[q]) {
        preStatus = stopReason = "EXACTLY_PROVEN_QUERY_INFEASIBLE";
        queryExact = true;
        return finish();
    }
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive2, comp, comps);
    compId = comp[q];
    compSize = (int)comps[compId].size();
    for (int e = G.off[q]; e < G.off[q + 1]; e++) if (alive2[G.adj[e]]) qDeg++;
    // (5) warm start seeded by {q}: contains q by construction, then verified;
    //     an unusable or q-free warm start is never installed as incumbent.
    //     SHARED across both variants: the incumbent reaches
    //     the search only through pruneThresh(), which only Bounding-family code
    //     reads, so it cannot prune when bounding is off).
    GadgetFinder gf(G, C, alive2, inf);
    SolveResult Rw = solve_lift(G, C, alive2, comps, inf, gf, &Q);
    {
        string why;
        warmOk = !Rw.S.empty() && verify_community(G, C, Rw.S, C.budget, why);
        if (find(Rw.S.begin(), Rw.S.end(), q) == Rw.S.end()) warmOk = false;
        if (warmOk) { warmScore = Rw.score1; warmSize = Rw.S.size(); warmCost = Rw.cost; }
    }
    // (6) exact search over F(q): q force-included, only q's component searched
    ExactBnB ex(G, C, inf);
    ex.nodeCap = nodeCap; ex.timeCap = timeCap; ex.epsFrac = epsFrac;
    ex.algo = &algo;
    ex.run_query(comps, warmOk ? Rw.S : vector<int>{}, Q);
    visNodes = ex.nodes; incUpd = ex.incumbentUpdates;
    ballTrunc = ex.ballTruncations;
    coverSkipTrunc = ex.coveringSkippedOnTrunc;
    dkSkipTrunc = ex.dkSkippedOnTrunc;
    cCascade = ex.cntCascadeRemovals; cForced = ex.cntForcedInclusions;
    cTwinSkip = ex.cntTwinBranchSkips; cBndCalls = ex.cntBoundCalls;
    cBndPrunes = ex.cntBoundPrunes; cComplPrunes = ex.cntCompletionPrunes;
    cMrvNodes = ex.cntMrvNodes; cRankNodes = ex.cntRankNodes;
    cNeutralNodes = ex.cntNeutralOrderNodes;
    ubFromSearch = ex.ubFromSearch();
    double scale = (double)inf.nT / (double)max<ll>(C.rr1, 1);
    bestScore = ex.bestRaw < 0 ? 0 : scale * (double)ex.bestRaw;
    ub = scale * ex.certifiedUBraw();
    {   // root-level knapsack UB is often tighter than truncation records
        ll rough = 0;
        for (auto& cm2 : comps)
            rough = max(rough, min(ub_component(inf, cm2),
                                   ub_frac_knapsack(G, inf, cm2, C.budget)));
        ub = min(ub, scale * (double)rough);
        ub = max(ub, bestScore);
    }
    hitNodeCap = false;  // retained in output schema; node caps are no longer enforced
    timedOut = !ex.complete;
    if (!ex.bestS.empty()) {   // independent verification incl. q-containment
        string why;
        bool okv = verify_community(G, C, ex.bestS, C.budget, why) &&
                   find(ex.bestS.begin(), ex.bestS.end(), q) != ex.bestS.end();
        if (!okv) {
            stopReason = "INTERNAL_VERIFY_FAILED";   // defensive; not expected
            return finish();
        }
        feasible = true;
        bestS = ex.bestS;
        bestCost = GadgetFinder::cost_of(G, bestS);
    }
    if (ex.complete) {
        queryExact = true;
        stopReason = feasible ? "QUERY_EXACT_FEASIBLE"
                              : "EXACTLY_PROVEN_QUERY_INFEASIBLE";
    } else if (feasible) {
        stopReason = "QUERY_TIMEOUT_WITH_INCUMBENT";
    } else {
        stopReason = "NO_FEASIBLE_FOUND_BEFORE_TIMEOUT";
    }
    return finish();
}

// ---------------------------------------------------- query_heuristic mode
// Heuristic-only feasibility validation for a single query vertex.
// Same loading, exact static reductions and anchored preprocessing as
// query_exact (type check, cost check, peel, Dijkstra-peel fixpoint), but
// NO Branch-and-Bound. A ladder of verified constructions stops at the
// FIRST community that passes the independent exact checker
// verify_community() AND contains q. One-sided guarantee:
//   feasible_found=yes -> exact-verified feasible community (attached)
//   feasible_found=no  -> stop_reason=HEURISTIC_NOT_FOUND; NOT a proof of
//                         infeasibility.
// Static stop reasons (INVALID_QUERY_TYPE / STATIC_QUERY_INFEASIBLE_COST /
// STATIC_QUERY_NOT_IN_CANDIDATE_COMPONENT / EXACTLY_PROVEN_QUERY_INFEASIBLE)
// are inherited from query_exact's exact reductions; they remain
// exact proofs. Ladder:
//   H0  GadgetFinder::compute(q) with config knobs (warm-start
//       primitive, deterministic, reused verbatim);
//   H1  deterministic BFS balls with escalating caps -> protected peel
//       (q never removed) -> anchored shrink -> cost-desc minimize;
//   H2  closure-greedy warm lift seeded {q};
//   H3/H4 (alternating, seeded rng, --restarts) randomized-ball protected
//       peel, and deficit-driven construct&repair; both consolidated
//       through the same local cascade + minimize before verification.

// protected peel over 'mem': like GadgetFinder::cascade_component but the
// vertex 'protectV' is never removed; returns protectV's surviving
// component only if protectV's own typed-degree constraints hold at the
// fixpoint (so every returned member satisfies all constraints inside the
// returned set). Optionally reports protectV's residual deficit on failure.
static bool protected_peel_component(const HIN& G, const Cfg& C,
                                     const vector<int>& mem, int protectV,
                                     vector<int>& out, ll* qDefOut = nullptr) {
    int m = (int)mem.size();
    static thread_local vector<int> gid;
    if ((int)gid.size() < G.n) gid.assign(G.n, -1);
    for (int i = 0; i < m; i++) gid[mem[i]] = i;
    vector<char> alive(m, 1);
    vector<vector<int>> cnt(m);
    for (int i = 0; i < m; i++) {
        int v = mem[i];
        auto& cs = C.consOf[G.type[v]];
        cnt[i].assign(cs.size(), 0);
        for (int e = G.off[v]; e < G.off[v + 1]; e++) {
            int j = gid[G.adj[e]];
            if (j < 0) continue;
            for (size_t x = 0; x < cs.size(); x++)
                if (cs[x].first == G.type[G.adj[e]]) cnt[i][x]++;
        }
    }
    auto viol = [&](int i) {
        auto& cs = C.consOf[G.type[mem[i]]];
        for (size_t x = 0; x < cs.size(); x++)
            if (cnt[i][x] < cs[x].second) return true;
        return false;
    };
    int pi = gid[protectV];
    queue<int> qq;
    for (int i = 0; i < m; i++) if (i != pi && viol(i)) qq.push(i);
    while (!qq.empty()) {
        int i = qq.front(); qq.pop();
        if (!alive[i] || !viol(i)) continue;
        alive[i] = 0;
        int v = mem[i];
        for (int e = G.off[v]; e < G.off[v + 1]; e++) {
            int j = gid[G.adj[e]];
            if (j < 0 || !alive[j]) continue;
            auto& cs = C.consOf[G.type[mem[j]]];
            bool hit = false;
            for (size_t x = 0; x < cs.size(); x++)
                if (cs[x].first == G.type[v]) { cnt[j][x]--; hit = true; }
            if (hit && j != pi && viol(j)) qq.push(j);
        }
    }
    bool good = (pi >= 0) && !viol(pi);
    if (!good && qDefOut && pi >= 0) {
        ll d = 0;
        auto& cs = C.consOf[G.type[protectV]];
        for (size_t x = 0; x < cs.size(); x++)
            d += max(0, cs[x].second - cnt[pi][x]);
        *qDefOut = d;
    }
    out.clear();
    if (good) {
        vector<char> vis(m, 0); vector<int> bq = {pi}; vis[pi] = 1;
        for (size_t h = 0; h < bq.size(); h++) {
            int i = bq[h]; out.push_back(mem[i]);
            int v = mem[i];
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int j = gid[G.adj[e]];
                if (j >= 0 && alive[j] && !vis[j]) { vis[j] = 1; bq.push_back(j); }
            }
        }
        sort(out.begin(), out.end());
    }
    for (int i = 0; i < m; i++) gid[mem[i]] = -1;
    return good;
}

static int mode_query_heuristic(const string& gpath, const string& cpath,
                                ull seed, const string& qArg, double budgetOv,
                                int restarts, double timeCap) {
    HIN G; Cfg C;
    if (!load_graph(gpath, G)) { fprintf(stderr, "cannot read graph %s\n", gpath.c_str()); return 2; }
    if (!load_config(cpath, C)) { fprintf(stderr, "cannot read config %s\n", cpath.c_str()); return 2; }
    if (budgetOv > 0) C.budget = budgetOv;
    if (!finalize_loaded_config(C, G.ntypes)) return 2;
    if (qArg.empty() || qArg.find(',') != string::npos) {
        fprintf(stderr, "query_heuristic: need a single --query <vertex-id>\n");
        return 2;
    }
    int q = -1;
    try { q = stoi(qArg); } catch (...) { q = -1; }
    if (q < 0 || q >= G.n) {
        fprintf(stderr, "query_heuristic: bad vertex id '%s'\n", qArg.c_str());
        return 2;
    }
    // ---- result fields, printed once by finish() ---------------------------
    string preStatus = "OK", stopReason = "", method = "none";
    bool feasible = false, timedOut = false;
    int attempted = 0, verifyRejects = 0;
    ll diagMinDef = -1; size_t diagDefSize = 0; double diagDefCost = 0;
    double diagClosedCost = -1;             // cheapest exactly-closed-but-over-budget set seen
    int compId = -1, compSize = 0, qDeg = 0;
    vector<int> bestS;
    auto t0 = chrono::steady_clock::now();
    auto deadline = [&]() { return secs_since(t0) > timeCap; };
    auto finish = [&]() -> int {
        // independent per-check verification, recomputed from scratch here
        const char* na = "na";
        string vQin = na, vBud = na, vCon = na, vDeg = na, vAS = na, vfyWhy = na;
        double bCost = 0;
        if (!bestS.empty()) {
            bCost = GadgetFinder::cost_of(G, bestS);
            vQin = binary_search(bestS.begin(), bestS.end(), q) ? "yes" : "no";
            vBud = (bCost <= C.budget + 1e-9 + 1e-12 * fabs(C.budget)) ? "yes" : "no";
            vector<char> in(G.n, 0);
            for (int v : bestS) in[v] = 1;
            bool asOk = true, degOk = true;
            for (int v : bestS) {
                if (!C.inAS[G.type[v]]) { asOk = false; break; }
                for (auto& pr : C.consOf[G.type[v]]) {
                    int have = 0;
                    for (int e = G.off[v]; e < G.off[v + 1]; e++)
                        if (in[G.adj[e]] && G.type[G.adj[e]] == pr.first) have++;
                    if (have < pr.second) { degOk = false; break; }
                }
                if (!degOk) break;
            }
            vAS = asOk ? "yes" : "no"; vDeg = degOk ? "yes" : "no";
            queue<int> bq; bq.push(bestS[0]);
            vector<char> vis(G.n, 0); vis[bestS[0]] = 1; size_t cc = 1;
            while (!bq.empty()) {
                int v = bq.front(); bq.pop();
                for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                    int u = G.adj[e];
                    if (in[u] && !vis[u]) { vis[u] = 1; cc++; bq.push(u); }
                }
            }
            vCon = (cc == bestS.size()) ? "yes" : "no";
            string why2; verify_community(G, C, bestS, C.budget, why2);
            vfyWhy = why2;
            if (feasible && !(vQin == string("yes") && vBud == string("yes") &&
                              vCon == string("yes") && vDeg == string("yes") &&
                              vAS == string("yes") && vfyWhy == "ok")) {
                feasible = false;                       // defensive; not expected
                stopReason = "INTERNAL_VERIFY_FAILED";
            }
        }
        printf("query_heuristic: mode=query_heuristic dataset=%s\n", gpath.c_str());
        printf("query_heuristic: config=%s\n", cpath.c_str());
        printf("query_heuristic: budget=%.4f seed=%llu\n", C.budget, (unsigned long long)seed);
        printf("query_heuristic: query_id=%d query_type=%d target_type=%d query_cost=%.6f\n",
               q, G.type[q], C.target_type, G.cost[q]);
        printf("query_heuristic: query_component_id=%d query_component_size=%d query_degree=%d\n",
               compId, compSize, qDeg);
        printf("query_heuristic: query_preprocessing_status=%s\n", preStatus.c_str());
        printf("query_heuristic: heuristic_restarts=%d restarts_attempted=%d method=%s\n",
               restarts, attempted, method.c_str());
        printf("query_heuristic: feasible_found=%s timeout=%s stop_reason=%s\n",
               feasible ? "yes" : "no", timedOut ? "yes" : "no", stopReason.c_str());
        vector<int> tc(G.ntypes, 0);
        for (int v : bestS) tc[G.type[v]]++;
        printf("query_heuristic: community_size=%zu community_cost=%.4f community_types=",
               bestS.size(), bCost);
        for (int t = 0; t < G.ntypes; t++) printf("%s%d:%d", t ? "," : "", t, tc[t]);
        printf("\n");
        printf("query_heuristic: query_included=%s budget_valid=%s connectivity_valid=%s "
               "constraints_valid=%s types_in_AS=%s verify=%s\n",
               vQin.c_str(), vBud.c_str(), vCon.c_str(), vDeg.c_str(), vAS.c_str(), vfyWhy.c_str());
        printf("query_heuristic: heuristic_min_total_deficit=%lld at_size=%zu at_cost=%.4f "
               "closed_over_budget_min_cost=%.4f\n",
               diagMinDef, diagDefSize, diagDefCost, diagClosedCost);
        printf("query_heuristic: candidate_verify_rejects=%d\n", verifyRejects);
        printf("query_heuristic: heuristic_runtime=%.2fs\n", secs_since(t0));
        printf("query_heuristic: best_node_list=");
        for (int v : bestS) printf(" %d", v);
        printf("\n");
        return 0;
    };
    // (1)-(4): identical exact reductions to query_exact ---------------------
    if (G.type[q] != C.target_type) {
        preStatus = stopReason = "INVALID_QUERY_TYPE";
        return finish();
    }
    if (G.cost[q] > C.budget + 1e-9 + 1e-12 * fabs(C.budget)) {
        preStatus = stopReason = "STATIC_QUERY_INFEASIBLE_COST";
        return finish();
    }
    mt19937_64 rng(seed);
    Influence inf; inf.init(G, C, rng);
    vector<char> member(G.n, 1), alive;
    peel_core(G, C, member, alive);
    if (!alive[q]) {
        preStatus = stopReason = "STATIC_QUERY_NOT_IN_CANDIDATE_COMPONENT";
        return finish();
    }
    vector<int> Q = {q};
    double cQ = G.cost[q];
    vector<char> alive2 = alive;
    vector<char> isQ(G.n, 0);
    isQ[q] = 1;
    for (int pass = 0; pass < 5; pass++) {
        vector<double> dist(G.n, 1e300);
        priority_queue<pair<double,int>, vector<pair<double,int>>,
                       greater<pair<double,int>>> pq;
        dist[q] = 0; pq.push({0, q});
        while (!pq.empty()) {
            auto pr2 = pq.top(); pq.pop();
            double d = pr2.first; int v = pr2.second;
            if (d > dist[v]) continue;
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e];
                if (!alive2[u]) continue;
                double nd = d + (isQ[v] ? 0.0 : G.cost[v]);
                if (nd < dist[u] - 1e-12) { dist[u] = nd; pq.push({nd, u}); }
            }
        }
        vector<char> keep(G.n, 0);
        int removed = 0;
        for (int v = 0; v < G.n; v++) {
            if (!alive2[v]) continue;
            if (isQ[v] || cQ + dist[v] + G.cost[v] <= C.budget + 1e-9) keep[v] = 1;
            else removed++;
        }
        int c0 = 0; for (int v = 0; v < G.n; v++) c0 += alive2[v];
        vector<char> nextAlive;
        peel_core(G, C, keep, nextAlive);
        int c1 = 0; for (int v = 0; v < G.n; v++) c1 += nextAlive[v];
        alive2 = nextAlive;
        if (removed == 0 && c1 == c0) break;
    }
    if (!alive2[q]) {
        preStatus = stopReason = "EXACTLY_PROVEN_QUERY_INFEASIBLE";
        return finish();
    }
    vector<int> comp; vector<vector<int>> comps;
    components_of(G, alive2, comp, comps);
    compId = comp[q];
    compSize = (int)comps[compId].size();
    for (int e = G.off[q]; e < G.off[q + 1]; e++) if (alive2[G.adj[e]]) qDeg++;
    // ---- heuristic ladder ---------------------------------------------------
    GadgetFinder gfBase(G, C, alive2, inf);          // cascade and gadget provider
    // strict=true: the construction claims exact closure, so any non-budget
    // verify failure is counted as an implementation-error signal. The
    // warm-lift candidate is exempt (solve_lift commits the bare kernel {q};
    // q's own constraint may legitimately be unmet, as in query_exact).
    auto try_install = [&](vector<int> S, const string& how, bool strict) -> bool {
        if (S.empty()) return false;
        sort_uniq(S);
        if (!binary_search(S.begin(), S.end(), q)) return false;
        string why;
        if (!verify_community(G, C, S, C.budget, why)) {
            if (why == "over budget") {
                double cc = GadgetFinder::cost_of(G, S);
                if (diagClosedCost < 0 || cc < diagClosedCost) diagClosedCost = cc;
            } else if (strict) {
                verifyRejects++;                     // construction bug signal
            }
            return false;
        }
        bestS = S; method = how; feasible = true;
        return true;
    };
    auto note_deficit = [&](ll d, size_t sz, double cst) {
        if (diagMinDef < 0 || d < diagMinDef) { diagMinDef = d; diagDefSize = sz; diagDefCost = cst; }
    };
    // anchored shrink: drop far/expensive nodes in chunks, re-peel (q protected)
    auto shrink_anchored = [&](vector<int>& S, int targetSize) -> bool {
        while ((int)S.size() > targetSize) {
            if (deadline()) return false;
            map<int,int> distm; distm[q] = 0;
            vector<int> bq2 = {q};
            vector<char> inSet(G.n, 0);
            for (int v : S) inSet[v] = 1;
            for (size_t h = 0; h < bq2.size(); h++) {
                int v = bq2[h];
                for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                    int u = G.adj[e];
                    if (inSet[u] && !distm.count(u)) {
                        distm[u] = distm[v] + 1; bq2.push_back(u);
                    }
                }
            }
            vector<int> order = S;
            sort(order.begin(), order.end(), [&](int a, int b) {
                int da = distm.count(a) ? distm[a] : 1 << 28;
                int db = distm.count(b) ? distm[b] : 1 << 28;
                if (da != db) return da > db;
                return G.cost[a] > G.cost[b];
            });
            int chunk = max(1, (int)S.size() / 8);
            vector<char> drop(G.n, 0);
            int dropped = 0;
            for (int v : order) {
                if (dropped >= chunk) break;
                if (v == q) continue;
                drop[v] = 1; dropped++;
            }
            vector<int> mem2;
            for (int v : S) if (!drop[v]) mem2.push_back(v);
            vector<int> nc;
            if (!protected_peel_component(G, C, mem2, q, nc)) return false;
            if (nc.empty() || (int)nc.size() >= (int)S.size()) return false;
            S = std::move(nc);
        }
        return true;
    };
    // cost-desc anchored minimization (bounded; assumes S sorted, q in S)
    auto minimize_anchored = [&](vector<int>& S) {
        if ((int)S.size() > 1500 && !shrink_anchored(S, 1200)) return;
        for (int pass = 0; pass < max(1, C.minimize_passes); pass++) {
            vector<int> order = S;
            sort(order.begin(), order.end(), [&](int a, int b) {
                if (G.cost[a] != G.cost[b]) return G.cost[a] > G.cost[b];
                return inf.cov1[a].size() < inf.cov1[b].size();
            });
            bool changed = false;
            int steps = 0;
            for (int w : order) {
                if (w == q) continue;
                if ((++steps & 255) == 0 && deadline()) return;
                if (!binary_search(S.begin(), S.end(), w)) continue;
                vector<int> nc;
                if (gfBase.cascade_component(S, q, w, nc) &&
                    GadgetFinder::cost_of(G, nc) <
                        GadgetFinder::cost_of(G, S) - 1e-12) {
                    S = std::move(nc); changed = true;
                }
            }
            if (!changed) break;
        }
    };
    // ball attempt: BFS ball around q in alive2 (deterministic or randomized
    // neighbor order), protected peel, shrink, minimize
    auto ball_attempt = [&](int cap, int hops, bool randomized,
                            const string& how) -> bool {
        vector<int> ball; ball.reserve(cap);
        vector<char> inB(G.n, 0);
        vector<pair<int,int>> bq2; bq2.push_back({q, 0});
        inB[q] = 1; ball.push_back(q);
        vector<int> nbr;
        for (size_t h = 0; h < bq2.size() && (int)ball.size() < cap; h++) {
            auto pr2 = bq2[h];
            int x = pr2.first, d = pr2.second;
            if (d >= hops) continue;
            nbr.clear();
            for (int e = G.off[x]; e < G.off[x + 1]; e++) {
                int u = G.adj[e];
                if (alive2[u] && !inB[u]) nbr.push_back(u);
            }
            if (randomized) shuffle(nbr.begin(), nbr.end(), rng);
            else sort(nbr.begin(), nbr.end(), [&](int a, int b) {
                if (G.cost[a] != G.cost[b]) return G.cost[a] < G.cost[b];
                return a < b;
            });
            for (int u : nbr) {
                if ((int)ball.size() >= cap) break;
                inB[u] = 1; ball.push_back(u); bq2.push_back({u, d + 1});
            }
        }
        sort(ball.begin(), ball.end());
        vector<int> S; ll qd = 0;
        if (!protected_peel_component(G, C, ball, q, S, &qd)) {
            note_deficit(qd, ball.size(), GadgetFinder::cost_of(G, ball));
            return false;
        }
        minimize_anchored(S);
        return try_install(S, how, true);
    };
    // deficit-driven construct & repair (one randomized restart)
    auto construct_attempt = [&]() -> bool {
        vector<int> S = {q};
        vector<char> inS(G.n, 0); inS[q] = 1;
        double cS = G.cost[q];
        map<int, vector<int>> have;
        auto ensure_have = [&](int v) -> vector<int>& {
            auto it = have.find(v);
            if (it != have.end()) return it->second;
            auto& cs = C.consOf[G.type[v]];
            vector<int> h(cs.size(), 0);
            for (int e = G.off[v]; e < G.off[v + 1]; e++) {
                int u = G.adj[e];
                if (!inS[u]) continue;
                for (size_t x = 0; x < cs.size(); x++)
                    if (cs[x].first == G.type[u]) h[x]++;
            }
            return have.emplace(v, std::move(h)).first->second;
        };
        auto deficit_of = [&](int v) -> int {
            auto& cs = C.consOf[G.type[v]];
            auto& h = ensure_have(v);
            int d = 0;
            for (size_t x = 0; x < cs.size(); x++)
                d += max(0, cs[x].second - h[x]);
            return d;
        };
        auto add_node = [&](int u) {
            inS[u] = 1; S.push_back(u); cS += G.cost[u];
            ensure_have(u);
            for (int e = G.off[u]; e < G.off[u + 1]; e++) {
                int w = G.adj[e];
                if (!inS[w]) continue;
                auto it = have.find(w);
                if (it == have.end()) continue;
                auto& cs = C.consOf[G.type[w]];
                for (size_t x = 0; x < cs.size(); x++)
                    if (cs[x].first == G.type[u]) it->second[x]++;
            }
        };
        auto remove_node = [&](int u) {
            inS[u] = 0; cS -= G.cost[u];
            S.erase(find(S.begin(), S.end(), u));
            have.erase(u);
            for (int e = G.off[u]; e < G.off[u + 1]; e++) {
                int w = G.adj[e];
                if (!inS[w]) continue;
                auto it = have.find(w);
                if (it == have.end()) continue;
                auto& cs = C.consOf[G.type[w]];
                for (size_t x = 0; x < cs.size(); x++)
                    if (cs[x].first == G.type[u]) it->second[x]--;
            }
        };
        const int MAXADD = 600, MAXREPAIR = 40, SCANCAP = 4000;
        int adds = 0, repairs = 0;
        while (true) {
            if (deadline()) return false;
            vector<int> defs; ll total = 0;
            for (int v : S) {
                int d = deficit_of(v);
                if (d > 0) { defs.push_back(v); total += d; }
            }
            note_deficit(total, S.size(), cS);
            if (total == 0) {
                vector<int> s2 = S, nc;
                sort(s2.begin(), s2.end());
                if (!gfBase.cascade_component(s2, q, -1, nc)) return false;
                minimize_anchored(nc);
                return try_install(nc, "construct", true);
            }
            if (adds >= MAXADD) return false;
            // candidates = alive2 non-members of a type some deficient node needs
            map<int, int> red;
            for (int v : defs) {
                auto& cs = C.consOf[G.type[v]];
                auto& h = ensure_have(v);
                int deg = G.off[v + 1] - G.off[v];
                if (deg == 0) continue;
                int start = (int)(rng() % (ull)deg);
                for (size_t x = 0; x < cs.size(); x++) {
                    if (h[x] >= cs[x].second) continue;
                    int needT = cs[x].first, scanned = 0;
                    for (int t = 0; t < deg && scanned < SCANCAP; t++, scanned++) {
                        int u = G.adj[G.off[v] + ((start + t) % deg)];
                        if (!alive2[u] || inS[u] || G.type[u] != needT) continue;
                        red[u]++;
                    }
                }
            }
            if (red.empty()) {                        // stuck: repair
                if (repairs >= MAXREPAIR) return false;
                int worst = -1, wd = -1; double wc = -1;
                for (int v : defs) if (v != q) {
                    int d = deficit_of(v);
                    if (d > wd || (d == wd && G.cost[v] > wc)) {
                        worst = v; wd = d; wc = G.cost[v];
                    }
                }
                if (worst < 0) return false;          // only q deficient, no help
                remove_node(worst); repairs++;
                continue;
            }
            struct Cand { int u, red, ownNeed; double cost; size_t cov; };
            vector<Cand> cands; cands.reserve(red.size());
            for (auto& pr : red) {
                int u = pr.first;
                auto& cs = C.consOf[G.type[u]];
                vector<int> h(cs.size(), 0);
                int deg = G.off[u + 1] - G.off[u], scanned = 0;
                for (int t = 0; t < deg && scanned < SCANCAP; t++, scanned++) {
                    int w = G.adj[G.off[u] + t];
                    if (!inS[w]) continue;
                    for (size_t x = 0; x < cs.size(); x++)
                        if (cs[x].first == G.type[w]) h[x]++;
                }
                int need = 0;
                for (size_t x = 0; x < cs.size(); x++)
                    need += max(0, cs[x].second - h[x]);
                cands.push_back({u, pr.second, need, G.cost[u], inf.cov1[u].size()});
            }
            sort(cands.begin(), cands.end(), [](const Cand& a, const Cand& b) {
                if (a.red != b.red) return a.red > b.red;         // deficit cut
                if (a.ownNeed != b.ownNeed) return a.ownNeed < b.ownNeed;
                if (a.cost != b.cost) return a.cost < b.cost;
                return a.cov > b.cov;                              // influence
            });
            int K = (int)min<size_t>(cands.size(), 5);
            const Cand& pickc = cands[(size_t)(rng() % (ull)K)];
            if (cS + pickc.cost > C.budget + 1e-9) {   // budget-stuck: repair
                if (repairs < MAXREPAIR) {
                    int worst = -1; double wc = -1;
                    for (int v : S) if (v != q && G.cost[v] > wc) {
                        wc = G.cost[v]; worst = v;
                    }
                    if (worst >= 0 && wc > pickc.cost + 1e-12) {
                        remove_node(worst); repairs++;
                        continue;
                    }
                }
                return false;
            }
            add_node(pickc.u); adds++;
        }
    };
    // H0: warm-start gadget primitive with config knobs.
    if (!feasible && !deadline()) {
        gfBase.compute(q);
        if (gfBase.ok[q]) try_install(gfBase.K[q], "gadget_default", true);
    }
    // H1: deterministic escalating balls
    if (!feasible) {
        const int caps[] = {2000, 8000};
        const int hpss[] = {3, 4};
        for (int i = 0; i < 2 && !feasible && !deadline(); i++)
            ball_attempt(caps[i], hpss[i], false, "ball_det");
    }
    // H2: closure-greedy warm lift seeded by the query.
    if (!feasible && !deadline()) {
        SolveResult Rw = solve_lift(G, C, alive2, comps, inf, gfBase, &Q);
        if (!Rw.S.empty()) try_install(Rw.S, "warm_lift", false);
    }
    // H3/H4: alternating randomized restarts
    {
        const int caps[] = {800, 1600, 3200, 6400, 12800};
        for (int r = 0; r < restarts && !feasible; r++) {
            if (deadline()) { timedOut = true; break; }
            attempted++;
            if (r % 2 == 0)
                ball_attempt(caps[(r / 2) % 5], 3 + (r / 2) % 4, true, "rand_ball");
            else
                construct_attempt();
        }
    }
    if (!feasible && deadline()) timedOut = true;
    stopReason = feasible ? "HEURISTIC_FEASIBLE" : "HEURISTIC_NOT_FOUND";
    return finish();
}

static void print_public_help(FILE* out) {
    fprintf(out,
        "MIMCS public solver\n\n"
        "Usage:\n"
        "  mimcs --mode query_exact --algo advanced_full|baseline_enum\n"
        "        --graph FILE --config FILE --query V [--budget B]\n"
        "        [--seed S] [--timelimit SECONDS]\n"
        "  mimcs --mode config --graph FILE --config FILE\n"
        "  mimcs --mode selftest [--algo advanced_full|baseline_enum]\n"
        "        [--trials N] [--seed S]\n\n"
        "Public modes:\n"
        "  query_exact  Query-conditioned exact search. A time limit may return\n"
        "               an incumbent and certified upper bound before proof.\n"
        "  config       Validate and summarize a graph/configuration pair.\n"
        "  selftest     Compare an exact algorithm with brute force on generated\n"
        "               small instances.\n\n"
        "Algorithms:\n"
        "  advanced_full  MIMC-B&B (default)\n"
        "  baseline_enum  MIMC-Enum\n\n"
        "Unknown, duplicate, missing, or mode-inapplicable options are rejected.\n");
}

int main(int argc, char** argv) {
    string mode = "selftest", gpath, cpath, queryStr;
    string algoName = "advanced_full";
    int trials = 60; ull seed = 1;
    double budgetOv = 0, timeCap = 120.0;
    const double epsFrac = 0;
    const ll nodeCap = 50'000'000;
    bool help = false;
    set<string> seen;
    try {
        for (int i = 1; i < argc; i++) {
            string a = argv[i];
            if (!seen.insert(a).second)
                throw invalid_argument("duplicate option '" + a + "'");
            auto next = [&]() {
                if (i + 1 >= argc || string(argv[i + 1]).rfind("--", 0) == 0)
                    throw invalid_argument("missing value for '" + a + "'");
                return string(argv[++i]);
            };
            if (a == "--help" || a == "-h") help = true;
            else if (a == "--algo") algoName = next();
            else if (a == "--mode") mode = next();
            else if (a == "--trials") trials = stoi(next());
            else if (a == "--seed") seed = stoull(next());
            else if (a == "--graph") gpath = next();
            else if (a == "--config") cpath = next();
            else if (a == "--budget") budgetOv = stod(next());
            else if (a == "--query") queryStr = next();
            else if (a == "--timelimit") timeCap = stod(next());
            else throw invalid_argument("unknown option '" + a + "'");
        }
    } catch (const exception& e) {
        fprintf(stderr, "argument error: %s\nRun with --help for usage.\n", e.what());
        return 2;
    }
    if (help) { print_public_help(stdout); return 0; }

    const map<string, set<string>> allowed = {
        {"selftest", {"--mode", "--algo", "--trials", "--seed"}},
        {"config", {"--mode", "--graph", "--config"}},
        {"query_exact", {"--mode", "--algo", "--graph", "--config", "--query",
                         "--seed", "--budget", "--timelimit"}},
    };
    auto mi = allowed.find(mode);
    if (mi == allowed.end()) {
        fprintf(stderr, "unknown or non-public mode '%s'; valid modes: "
                        "query_exact, config, selftest\n", mode.c_str());
        return 2;
    }
    for (const string& opt : seen)
        if (opt != "--help" && opt != "-h" && !mi->second.count(opt)) {
            fprintf(stderr, "option '%s' is not valid with --mode %s\n",
                    opt.c_str(), mode.c_str());
            return 2;
        }
    if ((mode == "config" || mode == "query_exact") &&
        (gpath.empty() || cpath.empty())) {
        fprintf(stderr, "--mode %s requires --graph FILE and --config FILE\n",
                mode.c_str());
        return 2;
    }
    if (mode == "query_exact" && queryStr.empty()) {
        fprintf(stderr, "--mode query_exact requires --query V\n");
        return 2;
    }
    if (trials <= 0 || timeCap <= 0 || budgetOv < 0) {
        fprintf(stderr, "--trials and --timelimit must be positive; "
                        "--budget must be nonnegative\n");
        return 2;
    }
    // Validated algorithm-variant selection.  An unrecognised value is a hard
    // error: a run must never silently fall back to a different algorithm. The
    // default selects Advanced-Full.
    const AlgoCfg* algo = parse_algo(algoName);
    if (!algo) {
        fprintf(stderr, "unknown --algo '%s'; valid values: ", algoName.c_str());
        print_algo_names(stderr);
        fprintf(stderr, "\n");
        return 2;
    }
    if (mode == "selftest") return mode_selftest(trials, seed, *algo);
    if (mode == "config") return mode_config(gpath, cpath);
    if (mode == "query_exact") return mode_query_exact(gpath, cpath, seed, queryStr,
                                                       budgetOv, epsFrac, nodeCap, timeCap,
                                                       *algo);
    return 2;
}
