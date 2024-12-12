datatype Weight = W(int)
datatype Node = V(int)

datatype Edge = Edge(Node, Node, Weight)
datatype Graph = Graph(set<Node>, set<Edge >)

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

method Main(){
  var node1 := V(1);
  var node2 := V(2);
  var node3 := V(3);

  var edge1 := Edge(node1, node2, W(2));
  var edge2 := Edge(node2,node3, W(4));

  var graph1 := Graph({node1,node2,node3}, {edge1,edge2});
}