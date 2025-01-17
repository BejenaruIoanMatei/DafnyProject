datatype Node = V(id: int)
datatype New_Weight = W_new(val: MyInt)
datatype New_Edge = Edge_new(source: Node, destination: Node, weight: New_Weight)
datatype MyInt = Valid(n: int) | MinValue

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

      if 0 <= u < distance.Length && 0 <= v < distance.Length && 0 <= v < predecessor.Length
      {
        if distance[u] != MinValue && MyIntLessThan(MyIntAdd(distance[u], w), distance[v])
        {
          distance[v] := MyIntAdd(distance[u], w);
          predecessor[v] := u;
        }
      }
      j := j + 1;
    }
    i := i + 1;
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
  requires 0 <= source.id < distance.Length
  requires distance.Length > 0 && edges.Length > 0 && predecessor.Length > 0
  requires predecessor.Length == distance.Length
  modifies distance, predecessor
{
  var n := distance.Length;
  hasNegativeCycle := false;

  distance[source.id] := Valid(0);

  var i: nat := 0;

while i < n
  invariant 0 <= i <= n
  invariant forall k :: 0 <= k < i ==> (distance[k] == MinValue || k == source.id)
  invariant forall k :: 0 <= k < i ==> predecessor[k] == -1
{
  if i != source.id 
  {
    distance[i] := MinValue;
  }
  predecessor[i] := -1;
  i := i + 1;
}
  var k: nat := 0;
  while k < n - 1 {
    Relax_Edges(source, predecessor, edges, distance);
    k := k + 1;
  }

  hasNegativeCycle := Detect_Negative_Cycle(edges, distance);
}

method Main()

{
  // Construirea nodurilor
  var node1 := V(0);
  var node2 := V(1);
  var node3 := V(2);

  // Construirea greutăților
  var weight1 := W_new(Valid(5));
  var weight2 := W_new(Valid(3));
  var weight3 := W_new(Valid(-2));

  // Construirea muchiilor
  var edge1 := Edge_new(node1, node2, weight1); // muchie de la node1 la node2 cu greutate 5
  var edge2 := Edge_new(node2, node3, weight2); // muchie de la node2 la node3 cu greutate 3
  var edge3 := Edge_new(node3, node1, weight3); // muchie de la node3 la node1 cu greutate -2

  // Array-ul de muchii
  var edges := new New_Edge[3];
  edges[0] := edge1;
  edges[1] := edge2;
  edges[2] := edge3;

  // Inițializarea array-urilor de distanțe și predecesori
  var distance := new MyInt[3];
  var predecessor := new int[3];

  // Setarea valorilor implicite
  for i := 0 to 2 {
    distance[i] := MinValue;
    predecessor[i] := -1;
  }

  // Apelarea Bellman-Ford
  var hasNegativeCycle := BellmanFord(node1, predecessor, edges, distance);

  // Validarea rezultatelor
  print "Rezultate Bellman-Ford:\n";
  print "Distante:\n";
  for i := 0 to distance.Length - 1
  {
    if distance[i] == MinValue {
      print "Node ", i, ": Infinit\n";
    } else {
      match distance[i] {
        case Valid(n) => print "Node ", i, ": ", n, "\n";
        case MinValue => print "Node ", i, ": Infinit\n";
      }
    }
  }

  print "Predecesori:\n";
  for i := 0 to predecessor.Length - 1
  {
    print "Node ", i, ": ", predecessor[i], "\n";
  }

  if hasNegativeCycle {
    print "Graful are un ciclu negativ.\n";
  } else {
    print "Graful nu are un ciclu negativ.\n";
  }
}



