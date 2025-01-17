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


method dada(){
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
        case MinValue => true
        case Valid(m) => n < m
      }
  }
}

datatype New_Weight = W_new(val: MyInt)
datatype New_Edge = Edge_new(source: Node, destination: Node, weight: New_Weight)

ghost predicate Length_Ver(edges: seq<New_Edge>, distanceLength: nat)
{
  forall edge :: edge in edges ==>
                   0 <= edge.source.id < distanceLength && 0 <= edge.destination.id < distanceLength
}
method Relax_Edges(source: Node, predecessor: array<int>, edges: array<New_Edge>, distance: array<MyInt>)
  modifies distance, predecessor
  requires distance.Length > 0 && edges.Length > 0 && predecessor.Length > 0
  requires predecessor.Length == distance.Length
{
  var k: nat := 0;
  while k < distance.Length - 1
  {
    var j: nat := 0;
    while j < edges.Length
    {
      var edge := edges[j];
      var u := edge.source.id;
      var v := edge.destination.id;
      var w := edge.weight.val;

      if 0 <= u < distance.Length && 0 <= v < distance.Length
      {
        if distance[u] != MinValue
        {
          var newDist := MyIntAdd(distance[u], w);
          if newDist != MinValue && (distance[v] == MinValue || MyIntLessThan(newDist, distance[v]))
          {
            distance[v] := newDist;
            predecessor[v] := u;
          }
        }
      }
      j := j + 1;
    }
    k := k + 1;
  }
}


method Detect_Negative_Cycle(edges: array<New_Edge>, distance: array <MyInt>)
  returns (hasNegativeCycle: bool)
{
  hasNegativeCycle := false;

  if distance.Length == 0 || edges.Length == 0
  {
    return;
  }

  var j: nat := 0;

  while j < edges.Length
    invariant 0 <= j <= edges.Length
  {
    var edge := edges[j];
    var u := edge.source.id;
    var v := edge.destination.id;
    var w := edge.weight.val;

    if 0 <= u < distance.Length && 0 <= v < distance.Length
    {
      if distance[u] != MinValue && MyIntLessThan(MyIntAdd(distance[u], w), distance[v])
      {
        hasNegativeCycle := true;
        return;
      }
    }

    j := j + 1;
  }

}

method BellmanFord(source: Node, predecessor: array<int>, edges: array<New_Edge>, distance: array<MyInt>)
  returns (hasNegativeCycle: bool)
  modifies distance, predecessor
  requires distance.Length > 0 && edges.Length > 0 && predecessor.Length > 0
  requires predecessor.Length == distance.Length
  requires 0 <= source.id < distance.Length
{
  var i := 0;
  while i < distance.Length
    invariant 0 <= i <= distance.Length
  {
    distance[i] := MinValue;
    predecessor[i] := -1;
    i := i + 1;
  }

  distance[source.id] := Valid(0);


  Relax_Edges(source, predecessor, edges, distance);

  hasNegativeCycle := Detect_Negative_Cycle(edges, distance);
}

method Main()
{
  var node0 := V(0);
  var node1 := V(1);
  var node2 := V(2);
  var node3 := V(3);

  var edges := new New_Edge[5];
  edges[0] := Edge_new(node0, node1, W_new(Valid(4)));  // 0 -> 1 cu cost 4
  edges[1] := Edge_new(node0, node2, W_new(Valid(2)));  // 0 -> 2 cu cost 2
  edges[2] := Edge_new(node1, node2, W_new(Valid(-3))); // 1 -> 2 cu cost -3
  edges[3] := Edge_new(node2, node3, W_new(Valid(2)));  // 2 -> 3 cu cost 2
  edges[4] := Edge_new(node1, node3, W_new(Valid(3)));  // 1 -> 3 cu cost 3

  var distance := new MyInt[4];
  var predecessor := new int[4];

  var hasNegativeCycle := BellmanFord(node0, predecessor, edges, distance);

  print "Neg cicl ", hasNegativeCycle, "\n";
  print "Dist de la nodul sursa (0):\n";

  var i := 0;
  while i < distance.Length
  {
    print "La nodul ", i, ": ";
    match distance[i] {
      case MinValue => print "Infinit";
      case Valid(n) => print n;
    }
    print "\n";
    i := i + 1;
  }

  print "Pred:\n";
  i := 0;
  while i < predecessor.Length
  {
    print "Pentru nodul ", i, ": ", predecessor[i], "\n";
    i := i + 1;
  }
}