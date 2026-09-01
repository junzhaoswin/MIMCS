This is a dataset extracted from the PubMed.
The folder contains the following files:
1. vertex.txt
 Each line represents a vertex in PubMed. Each line starts with the vertex_id, following by vertex type.

2.edge.txt
 Each line represents an edge in PubMed. Each line starts with the edge_id, following by edge type.

3. graph.txt
 Each line represents an adjacent array. Each line starts with the vertex_id, following by a list of neighbor_vertex_id and edge_id.


The vertex types and edge types are numbered as follow:

<Gene> : 0;
<Disease> : 1;
<Chemical> : 2;
<Species> : 3;

<Gene->Disease> 0;
<Gene->Chemical> 1;
<Gene->Species> 2;
<Disease->Gene> : 3;
<Chemical->Gene> : 4;
<Species->Gene> : 5;

The number of gene vertices : 1186
The number of disease vertices : 5348
The number of chemical vertices : 6836
The number of species vertices : 886
The number of all vertices : 14256
The number of all directed edges : 67112
