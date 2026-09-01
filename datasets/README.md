# Datasets used in the MIMCS experiments

This directory holds the exact solver-format graphs used for the experiments in the paper and the small DBLP network used for the effectiveness case study. All files are gzip-compressed; decompress with `gunzip <file>.gz` (or `gzip -dk` to keep the archive).

## Solver-format graphs (Section 6, Table 3)

Each `<dataset>_logdeg.txt` file is in the input format described in the top-level README (`n m ntypes`, then one `type cost` line per vertex, then one `u v` line per undirected edge, zero-based implicit vertex ids). Vertex costs follow the experimental rule `c(v) = 1 + ln(1 + d(v))`. The vertex/edge counts are those reported in Table 3 of the paper.

| Dataset | File | Vertices | Edges | Vertex types | Type ids | Raw size | MD5 (raw) |
|---|---|---|---|---|---|---|---|
| DBLP | `dblp_logdeg.txt.gz` | 881,039 | 1,366,161 | 4 | 0 paper, 1 author, 2 venue, 3 topic | 28.4 MB | `5f044e5cecc35103b62a457a4ad55d2a` |
| IMDB | `imdb_logdeg.txt.gz` | 854,616 | 3,898,136 | 4 | 0 movie, 1 actor, 2 director (see configs for the types used) | 63.2 MB | `1c2f6f0e4890211891ad61984baa3e25` |
| TMDB | `tmdb_logdeg.txt.gz` | 71,978 | 113,581 | 7 | 0 movie, 1 cast, 3 country (see configs for the types used) | 2.0 MB | `0fe394710fe32b4ea2fb8b4bcb281859` |
| DBpedia | `dbpedia_logdeg.txt.gz` | 5,900,558 | 17,641,286 | 413 | numeric type ids; the experiments use types 0, 166, 181 (target 181) | 346.4 MB | `ad6d914f751f728fd7a9e880bf4bcbbd` |
| PubMed | `pubmed_logdeg.txt.gz` | 14,256 | 33,556 | 4 | 0 gene, 1 disease, 2 chemical, 3 species | 0.5 MB | `a1351f909a8b1ecfcb5e8d5ae94c0794` |

The three-type experimental settings (which vertex types participate, the target type, meta-paths, and relational constraints) are given as comments and fields in `experiments/configs/cfg_<dataset>_3T_S<setting>_G<gamma>.txt`; the type ids there refer to the type column of these graph files. DBLP, IMDB, TMDB, DBpedia, and PubMed are the public HIN datasets distributed with ICSH (Zhou et al., PVLDB 2023), converted to the solver format; `imdb_original_readme.txt` and `pubmed_original_readme.txt` are the original type/edge legends shipped with IMDB and PubMed.

## Case-study network (Section 6.2)

`case_study_small_dblp/` contains the small DBLP network used for the effectiveness case study: 37,791 vertices (14,475 authors, 14,376 papers, 20 venues, 8,920 topics) and 170,794 edges, extracted from the original DBLP network (the four-area DBLP subset).

| File | Content |
|---|---|
| `dblp_unit.txt.gz` | solver-format graph with unit vertex costs (type ids: 0 author, 1 paper, 2 venue, 3 topic) |
| `dblp_map.txt.gz` | vertex id to original entity (author name, paper title, venue, term) mapping |
| `raw_relations/paper_author.dat.gz`, `paper_conference.dat.gz`, `paper_type.dat.gz` | the raw relation files from which the graph was built |
| `icsh_format/graph.txt.gz`, `edge.txt.gz`, `vertex.txt.gz` | the same network in the input format of ICSH/SACH |
| `icsh_format/weight.txt.gz` | vertex importance values used by ICSH and SACH in the case study: one common PageRank (damping 0.85) computed on this network |

MD5 of the decompressed files:

| File | MD5 |
|---|---|
| `dblp_unit.txt` | `529e25caf20bc38b6807b066d110ce1d` |
| `dblp_map.txt` | `a61ef649fa7c691e8212215d3029f439` |
| `paper_author.dat` | `d1078a46e3288fd717c5b724a7f71b1e` |
| `paper_conference.dat` | `089f5772d56e8f1814c1c5401d9672a4` |
| `paper_type.dat` | `21e98cb2fe444b8309dc9ea9974a0a96` |
| `graph.txt` | `8472455c0388d705afd0511950be3611` |
| `edge.txt` | `c33aa654d68533c1b7150d39f6d9e996` |
| `vertex.txt` | `5f9890c814f2f43326b7b78a3779cb7f` |
| `weight.txt` | `21ac92f17451d185786e296ff74f8d46` |
