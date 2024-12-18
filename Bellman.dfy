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

datatype MyInt = Valid(n: int) | MinValue

method testMinValue(x: MyInt) returns (isMin: bool)
{
  isMin := match x {
    case MinValue => true
    case Valid(_) => false
  };
}

function MyIntToInt(x: MyInt): int
  requires x != MinValue
{
  match x {
    case Valid(n) => n
  }
}

function MyIntAdd(x: MyInt, y: MyInt): MyInt
{
  match x {
    case MinValue => MinValue
    case Valid(n) =>
      match y {
        case MinValue => MinValue
        case Valid(m) => Valid(n + m)
      }
  }
}

function MyIntLessThan(x: MyInt, y: MyInt): bool
{
  match x {
    case MinValue => false
    case Valid(n) =>
      match y {
        case MinValue => false
        case Valid(m) => n < m
      }
  }
}

/*
method RelaxEdges(distance: array<MyInt>, predecessor: array<int>, edges: array<Edge>)
  returns (success: bool)
  modifies distance, predecessor
{
  success := true;

  var i: nat := 0;

  while i < distance.Length - 1
    invariant 0 <= i <= distance.Length - 1
    invariant forall e :: e in edges && distance[e.source.id] != int.MinValue ==> distance[e.destination.id] <= distance[e.source.id] + e.weight.val
  {
    for i := 0 to |edges|

    {
      var egde := edges[i];
      var u, v, w := edge.0, edge.1, edge.2;

      if distance[u] != MyInt.MinValue && distance[u] + w < distance[v] {
        distance[v] := distance[u] + w;
        predecessor[v] := u;
      }
    }
    i := i + 1;
  }
  success := forall u, v, w :: (u, v, w) in edges && distance[u] != MyInt.MinValue ==> distance[v] <= distance[u] + w;
}
*/


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

