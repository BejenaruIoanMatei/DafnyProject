const infinity: int := 999999999

datatype Weight = W(val: int)
datatype Node = V(id: int)
datatype Edge = Edge(source: Node, destination: Node, weight: Weight)
datatype Graph = Graph(nodes: set<Node>, edges: set<Edge>)

function edge_weight(e: Edge): int
{
  match e
  case Edge(from_where, to_where, W(w)) => w
}

function from_where(e: Edge): Node
{
  match e
  case Edge(from_where, to_where, W(w)) => from_where
}

function to_where(e: Edge): Node
{
  match e
  case Edge(from_where, to_where, W(w)) => to_where
}

function nodes_in_graph(g: Graph): set<Node>
{
  match g
  case Graph(v, e) => v
}

function edges_in_graph(g: Graph): set<Edge>
{
  match g
  case Graph(v, e) => e
}

function edge_exists(g: Graph, e: Edge): bool
{
  e in edges_in_graph(g)
}

function node_exists(g: Graph, n: Node): bool
{
  n in nodes_in_graph(g)
}

function adjacent_nodes(g: Graph, n: Node): set<Node>
{
  var result := set<Node>(); 
  for e in edges_in_graph(g) {
    if from_where(e) == n then
      result := result + {to_where(e)} + adjacent_nodes(g, to_where(e)) y
    else if to_where(e) == n then
      result := result + {from_where(e)} + adjacent_nodes(g, from_where(e))
}

method Main() {
  // Define the nodes
  var node1 := V(1);
  var node2 := V(2);
  var node3 := V(3);

  // Define the edges
  var edge1 := Edge(node1, node2, W(2));
  var edge2 := Edge(node2, node3, W(4));

  // Create the graph with nodes and edges
  var graph1 := Graph({node1, node2, node3}, {edge1, edge2});

 

}
