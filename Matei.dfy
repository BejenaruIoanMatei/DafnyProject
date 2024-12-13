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

predicate isValid(graph: Graph)
{
  forall e :: e in graph.edges ==> e.source in graph.nodes && e.destination in graph.nodes
}

method Main(){
  var node1 := V(1);
  var node2 := V(2);
  var node3 := V(3);

  var edge1 := Edge(node1, node2, W(2));
  var edge2 := Edge(node2,node3, W(4));

  var graph1 := Graph({node1,node2,node3}, {edge1,edge2});
}

predicate EmptySet<T(==)>() { {} is set<T> }

method check_if_set_empty(s: set<int>) returns (IsEmpty:bool)
{
  IsEmpty := s == {};
}

method hasNegativeCycle(graph: Graph) returns (hasNegative: bool)
{
  var nodess := graph.nodes;
  var edgess := graph.edges;

  if nodess == {} {
    hasNegative := false;
    return;
  }
  else{
    hasNegative := true;
    return;
  }

}

