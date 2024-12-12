datatype Node = Node(id: int, neighbors: set<Node>)

class Graph
  {
  var nodes: set<Node>

  constructor(nodes: set<Node>)
  {
    this.nodes := nodes;
  }
}

function CreateNode(id: int): Node
{
  Node(id, {})
}

function AddNeighbors(node: Node, neighbors: set<Node>): Node
{
  Node(node.id, neighbors)
}

method Main() {
  var node1 := CreateNode(1);
  var node2 := CreateNode(2);
  var node3 := CreateNode(3);

  var updatedNode1 := AddNeighbors(node1, {node2, node3});
  var updatedNode2 := AddNeighbors(node2, {node1, node3});
  var updatedNode3 := AddNeighbors(node3, {node1, node2});

  var graph := new Graph({updatedNode1, updatedNode2, updatedNode3});
}