This is a dataset extracted from the IMDB network.
The folder contains the following files:
1. vertex.txt
 Each line represents a vertex in IMDB. Each line starts with the vertex_id, following by vertex type.

2.edge.txt
 Each line represents an edge in IMDB. Each line starts with the edge_id, following by edge type.

3. graph.txt
 Each line represents an adjacent array. Each line starts with the vertex_id, following by a list of neighbor_vertex_id and edge_id.


The vertex types and edge types are numbered as follow:

<Movie> : 0;
<Actor> : 1;
<Director> : 2;
<Writer> : 3;

<Movie->Actor> 0;
<Actor->Movie> 1;
<Movie->Director> 2;
<Director->Movie> : 3;
<Movie->Writer> : 4;
<Writer->Movie> : 5;

The number of movie vertices : 513278
The number of actor vertices : 54881
The number of director vertices : 84323
The number of writer vertices : 202134
The number of all vertices : 854616
The number of all directed edges : 7796288
