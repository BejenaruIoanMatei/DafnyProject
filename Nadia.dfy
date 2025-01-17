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




