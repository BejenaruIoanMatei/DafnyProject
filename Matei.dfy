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

datatype New_Weight = W_new(val: MyInt)
datatype New_Edge = Edge_new(source: Node, destination: Node, weight: New_Weight)

method Relax_Edges(source: Node, predecessor: array<int>, edges: array<New_Edge>, distance: array<MyInt>)
  modifies distance, predecessor
{
  if distance.Length == 0 || edges.Length == 0 || predecessor.Length == 0 {
    return;
  }

  var i: nat := 0;

  while i < distance.Length - 1
    invariant 0 <= i <= distance.Length - 1
  {
    var j: nat := 0;

    while j < edges.Length
      invariant 0 <= j <= edges.Length
    {
      var edge := edges[j];
      var u := edge.source.id;
      var v := edge.destination.id;
      var w := edge.weight.val;

      if 0 <= u < distance.Length && 0 <= v < distance.Length && 0 <= v < predecessor.Length {
        if distance[u] != MinValue && MyIntLessThan(MyIntAdd(distance[u], w), distance[v]) {
          distance[v] := MyIntAdd(distance[u], w);
          predecessor[v] := u;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
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

