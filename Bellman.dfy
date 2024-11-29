class Graph
  {
  var nodes: seq<Node>

  constructor(nodes: seq<Node>)
  {
    this.nodes := nodes;
  }

}

class Node
  {
  var id: int
  var neighbors: set<Node>

  constructor(id: int)
  {
    this.id := id;
    this.neighbors := {};
  }

}

method Main()
{
  var node1 := new Node(1);
  var node2 := new Node(2);
  var node3 := new Node(3);

  node1.neighbors := {node2, node3};
  node2.neighbors := {node1, node3};
  node3.neighbors := {node1, node2};

  var graph := new Graph([node1, node2, node3]);
}