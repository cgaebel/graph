//! Directed Graphs.
#![crate_type = "lib"]
#![feature(macro_rules, default_type_params)]
#![deny(warnings, missing_doc)]

use std::collections::Deque;
use std::collections::hashmap;
use std::collections::hashmap::{HashMap, HashSet};
use std::collections::ringbuf::RingBuf;
use std::iter;
use std::option;
use std::rc::Rc;

/// All the edges in a graph, tagged with parameter `E`.
pub type EdgeMap<E> = HashMap<uint, HashMap<uint, Rc<E>>>;

/// A graph is parameterized by data of your choice, so you can tag nodes and
/// edges with custom data.
///
/// This library was created to scratch my own itches. If you want to see more
/// methods implemented, I will be very responsive in merging patches.
#[deriving(Clone, PartialEq, Eq, Show)]
pub struct Graph<V, E> {
  nodes: HashMap<uint, V>,
  edges: EdgeMap<E>,

  // A reverse mapping of every edge. Useful for several algorithms (such as
  // cycle detection) and does not increase the asymptotic complexity.
  rev_edges: EdgeMap<E>,
}

pub type Verticies<'a, V> = hashmap::Entries<'a, uint, V>;

// An iterator through all the nodes connected to a node.
pub type Connections<'a, E> =
  iter::Map<'a,
    (uint, (&'a uint, &'a Rc<E>)),
    (uint, uint, Rc<E>),
    iter::Zip<
      iter::Repeat<uint>,
      iter::FlatMap<'a,
        &'a HashMap<uint, Rc<E>>,
        option::Item<&'a HashMap<uint, Rc<E>>>,
        hashmap::Entries<'a, uint, Rc<E>>>>>;

impl<V, E> Graph<V, E> {
  /// Construct a new, empty graph.
  pub fn new() -> Graph<V, E> {
    let g =
      Graph {
        nodes:     HashMap::new(),
        edges:     HashMap::new(),
        rev_edges: HashMap::new(),
      };

    g.invariant();

    g
  }

  /// Empty out the graph for reuse.
  pub fn clear(&mut self) {
    self.nodes = HashMap::new();
    self.clear_edges();
  }

  /// Remove all edges from the graph.
  pub fn clear_edges(&mut self) {
    self.edges     = HashMap::new();
    self.rev_edges = HashMap::new();
  }

  /// Returns an iterator over every node in the graph.
  pub fn verticies<'a>(&'a self) -> Verticies<'a, V> {
    self.nodes.iter()
  }

  /// Returns the number of verticies in the graph.
  pub fn number_of_verticies(&self) -> uint {
    self.nodes.len()
  }

  fn inner_number_of_edges(emap: &EdgeMap<E>) -> uint {
    emap.iter().map(|(_, es)| es.len()).fold(0, |x,y| x + y)
  }

  /// Returns the number of nodes in the graph.
  pub fn number_of_edges(&self) -> uint {
    Graph::<V, E>::inner_number_of_edges(&self.edges)
  }

  #[cfg(test)]
  fn create_directly(vs: Vec<(uint, V)>, es: Vec<(uint, uint, E)>) -> Graph<V, E> {
    let mut g = Graph::new();

    g.nodes = vs.move_iter().map(|(i, v)| (i, v)).collect();
    
    for (from, to, e) in es.move_iter() {
      let rce = Rc::new(e);

      let emap = g.edges.find_or_insert_with(from, |_| HashMap::new());
      emap.insert(to, rce.clone());

      let rmap = g.rev_edges.find_or_insert_with(to, |_| HashMap::new());
      rmap.insert(from, rce);
    }

    g.invariant();

    g
  }

  #[cfg(test)]
  fn invariant(&self) {
    for (from, tos) in self.edges.iter() {
      assert!(self.nodes.contains_key(from));
      for to in tos.keys() {
        assert!(self.nodes.contains_key(to));
        match self.rev_edges.find(to) {
          None => fail!("{} was not found in the rev map.", &to),
          Some(r_map) => {
            assert!(r_map.contains_key(from));
          }
        }
      }
    }

    let num_edges     = Graph::<V, E>::inner_number_of_edges(&self.edges);
    let num_rev_edges = Graph::<V, E>::inner_number_of_edges(&self.rev_edges);
    assert_eq!(num_edges, num_rev_edges);
  }

  #[cfg(not(test))]
  fn invariant(&self) {}

  /// Inserts a vertex into the graph. If such a vertex already exists
  /// (possibly with another tag), the new vertex will silently overwrite it.
  pub fn insert_vertex(&mut self, val: uint, v: V) {
    self.nodes.insert(val, v);
    self.invariant();
  }

  fn contains_vertex(&self, val: uint) -> bool {
    self.nodes.contains_key(&val)
  }

  fn ensure_has_vertex(&self, v: uint) {
    if !self.contains_vertex(v) {
      fail!("Vertex {} does not exist in the graph.", v);
    }
  }

  /// Inserts an edge from `from` to `to`, with label `e`. If such an edge
  /// already exists (possibly with another tag), the new edge will silently
  /// overwrite it.
  ///
  /// If the given vertexes do not exist in the graph, this will fail.
  pub fn insert_directed_edge(&mut self, from: uint, to: uint, e: E) {
    {
      self.ensure_has_vertex(from);
      self.ensure_has_vertex(to);

      let fwd_map = self.edges.find_or_insert_with(from, |_| HashMap::new());
      let rev_map = self.rev_edges.find_or_insert_with(to, |_| HashMap::new());

      let rce = Rc::new(e);
      fwd_map.insert(to, rce.clone());
      rev_map.insert(from, rce);
    }

    self.invariant();
  }

  fn inner_edges_from<'a>(edges: &'a EdgeMap<E>, v: uint) -> Connections<'a, E> {
    iter::Repeat::new(v)
      .zip(edges.find(&v).move_iter().flat_map(|m| m.iter()))
      .map(|(v, (&u, e))| (v, u, e.clone()))
  }

  /// Returns an iterator through all the nodes connected from `v`. i.e. every
  /// edge for which the source is `v`.
  pub fn edges_from<'a>(&'a self, v: uint) -> Connections<'a, E> {
    Graph::<V, E>::inner_edges_from(&self.edges, v)
  }

  fn inner_edges_to<'a>(rev_edges: &'a EdgeMap<E>, v: uint) -> Connections<'a, E> {
    iter::Repeat::new(v)
      .zip(rev_edges.find(&v).move_iter().flat_map(|m| m.iter()))
      .map(|(u, (&v, e))| (v, u, e.clone()))
  }

  /// Returns an iterator through all the edges connected to `v`. i.e. every
  /// edge for which the destination is `v`.
  pub fn edges_to<'a>(&'a self, v: uint) -> Connections<'a, E> {
    Graph::<V, E>::inner_edges_to(&self.rev_edges, v)
  }

  /// Returns true iff there are any edges from `v`.
  pub fn has_edges_from(&self, v: uint) -> bool {
    self.edges_from(v).next().is_some()
  }

  /// Returns true iff there are any edges to `v`.
  pub fn has_edges_to(&self, v: uint) -> bool {
    self.edges_to(v).next().is_some()
  }

  fn inner_remove_single_edge(edge_map: &mut EdgeMap<E>, from: uint, to: uint) {
    let mut removed_last_edge = false;

    match edge_map.find_mut(&from) {
      None => {},
      Some(es) => {
        es.remove(&to);
        if es.is_empty() {
          removed_last_edge = true;
        }
      }
    }

    if removed_last_edge {
      edge_map.remove(&from);
    }
  }

  fn inner_remove_edge(edges: &mut EdgeMap<E>, rev_edges: &mut EdgeMap<E>, from: uint, to: uint) {
    Graph::<V, E>::inner_remove_single_edge(edges, from, to);
    Graph::<V, E>::inner_remove_single_edge(rev_edges, to, from);
  }

  /// Remove an edge from the graph. Does nothing if the edge does not exist.
  pub fn remove_edge(&mut self, from: uint, to: uint) {
    Graph::<V, E>::inner_remove_edge(&mut self.edges, &mut self.rev_edges, from, to)
  }

  /// Removes a vertex and any connected edges from the graph.
  pub fn remove_vertex(&mut self, v: uint) {
    let to_remove : Vec<(uint, uint)> =
      self.edges_to(v).chain(self.edges_from(v)).map(|(a, b, _)| (a, b)).collect();

    for &(from, to) in to_remove.iter() {
      self.remove_edge(from, to);
    }

    self.nodes.remove(&v);
  }

  /// Returns None if the graph is acyclic. Otherwise, returns the verticies
  /// of the graph in a linear order such that each node comes before all nodes
  /// to which it has outbound edges.
  pub fn topological_sort<'a>(&'a self) -> Option<Vec<(uint, &'a V)>> {
    // L ← Empty list where we put the sorted elements
    // Q ← Set of all nodes with no incoming edges
    // while Q is non-empty do
    //     remove a node n from Q
    //     insert n into L
    //     for each node m with an edge e from n to m do
    //         remove edge e from the graph
    //         if m has no other incoming edges then
    //             insert m into Q
    // if graph has edges then
    //     output error message (graph has a cycle)
    // else 
    //     output message (proposed topologically sorted order: L)

    let mut l = Vec::new();
    let mut q : RingBuf<(uint, &'a V)> =
      self.nodes.iter()
        .filter(|&(&n, _)| !self.has_edges_to(n))
        .map(|(&n, v)| (n, v))
        .collect();

    let mut edges : HashMap<uint, HashMap<uint, Rc<E>>> =
      self.edges.iter()
        .map(|(&u, es)|
          (u, es.iter().map(|(&v, e)| (v, e.clone())).collect()))
        .collect();

    let mut rev_edges : HashMap<uint, HashMap<uint, Rc<E>>> =
      self.rev_edges.iter()
        .map(|(&u, es)|
          (u, es.iter().map(|(&v, e)| (v, e.clone())).collect()))
        .collect();

    while !q.is_empty() {
      let (n, v) = q.pop_front().unwrap();
      l.push((n, v));
      let mut to_remove = Vec::new();
      for (_, m, _) in Graph::<V, E>::inner_edges_from(&edges, n) {
        to_remove.push((n, m));

        let edges_to_m : Vec<(uint, uint, Rc<E>)> =
          Graph::<V, E>::inner_edges_to(&rev_edges, m).collect();

        if edges_to_m.len() != 1 { continue; }

        let &(from, to, _) = edges_to_m.iter().next().unwrap();

        if from == n && to == m {
          q.push_back((m, self.nodes.find(&m).unwrap()));
        }
      }

      for (n, m) in to_remove.move_iter() {
        Graph::<V, E>::inner_remove_edge(
          &mut edges, &mut rev_edges, n, m);
      }
    }

    if edges.is_empty() {
      Some(l)
    } else {
      None
    }
  }

  /// Returns true iff the graph has no cycles.
  pub fn is_acyclic(&self) -> bool {
    self.topological_sort().is_some()
  }

  /// Perform a depth-first search starting at the given node.
  pub fn dfs<'a>(&'a self, starting_node: uint) -> Dfs<'a, V, E> {
    Dfs {
      graph:    self,
      visited:  HashSet::new(),
      to_visit: vec!(starting_node),
    }
  }

  /// Performs a breadth-first search starting at the given node.
  pub fn bfs<'a>(&'a self, starting_node: uint) -> Bfs<'a, V, E> {
    let mut to_visit = RingBuf::new();
    to_visit.push_back(starting_node);

    Bfs {
      graph:    self,
      visited:  HashSet::new(),
      to_visit: to_visit,
    }
  }
}

/// Iterator over the verticies in a depth first search
pub struct Dfs<'a, V, E> {
  graph:    &'a Graph<V, E>,
  visited:  HashSet<uint>,
  to_visit: Vec<uint>,
}

impl<'a, V, E> Iterator<(uint, &'a V)> for Dfs<'a, V, E> {
  fn next(&mut self) -> Option<(uint, &'a V)> {
    let u;

    loop {
      match self.to_visit.pop() {
        None => return None,
        Some(v) => {
          if !self.visited.contains(&v) {
            u = v;
            break;
          }
        }
      }
    }

    let v =
      match self.graph.nodes.find(&u) {
        None => return None,
        Some(v) => v
      };

    self.visited.insert(u);

    for (_, v, _) in self.graph.edges_from(u) {
      self.to_visit.push(v);
    }

    Some((u, v))
  }

  fn size_hint(&self) -> (uint, Option<uint>) {
    (0, Some(self.graph.number_of_verticies() - self.visited.len()))
  }
}

/// Iterator over the verticies in a depth first search
pub struct Bfs<'a, V, E> {
  graph:    &'a Graph<V, E>,
  visited:  HashSet<uint>,
  to_visit: RingBuf<uint>,
}

impl<'a, V, E> Iterator<(uint, &'a V)> for Bfs<'a, V, E> {
  fn next(&mut self) -> Option<(uint, &'a V)> {
    let u;

    loop {
      match self.to_visit.pop_front() {
        None => return None,
        Some(v) => {
          if !self.visited.contains(&v) {
            u = v;
            break;
          }
        }
      }
    }

    let v =
      match self.graph.nodes.find(&u) {
        None => return None,
        Some(v) => v
      };

    self.visited.insert(u);

    for (_, v, _) in self.graph.edges_from(u) {
      self.to_visit.push_back(v);
    }

    Some((u, v))
  }

  fn size_hint(&self) -> (uint, Option<uint>) {
    (0, Some(self.graph.number_of_verticies() - self.visited.len()))
  }
}

#[test]
fn test_create() {
  Graph::<(), ()>::new();
  Graph::<uint, uint>::new();
}

#[test]
fn test_add_verticies() {
  let mut g = Graph::new();

  for &x in [1,2,3,4].iter() {
    g.insert_vertex(x, ());
  }

  let expected =
    Graph::<(), ()>::create_directly(
      vec!((1,()),(2,()),(3,()),(4,())),
      vec!());

  assert_eq!(g, expected);
}

#[test]
fn test_insert_directed_edge() {
  let mut g = Graph::new();

  for &x in [1,2,3,4].iter() {
    g.insert_vertex(x, ());
  }

  g.insert_directed_edge(1, 3, ());
  g.insert_directed_edge(3, 1, ());

  let expected =
    Graph::<(), ()>::create_directly(
      vec!((1,()),(2,()),(3,()),(4,())),
      vec!((1,3,()),(3,1,())));

  assert_eq!(g, expected);
}

#[test]
fn test_edges_to_and_from() {
  let mut g = Graph::new();

  for &x in [1,2,3,4].iter() {
    g.insert_vertex(x, ());
  }

  g.insert_directed_edge(1,1,0);
  g.insert_directed_edge(1,2,1);
  g.insert_directed_edge(1,3,2);
  g.insert_directed_edge(4,1,3);

  {
    let expected =
      Graph::<(), uint>::create_directly(
        vec!((1,()),(2,()),(3,()),(4,())),
        vec!((1,1,0),(1,2,1),(1,3,2),(4,1,3)));

    assert_eq!(g, expected);
  }

  {
    let actual : Vec<(uint, uint, Rc<uint>)> =
      g.edges_to(2).collect();

    assert_eq!(actual, vec!((1,2,Rc::new(1))));
  }

  {
    let mut actual : Vec<(uint, uint, Rc<uint>)> =
      g.edges_to(1).collect();

    let mut expected : Vec<(uint, uint, Rc<uint>)> =
      vec!((1,1,Rc::new(0)),(4,1,Rc::new(3)));

    actual.sort();
    expected.sort();

    assert_eq!(actual, expected);
  }


  {
    let mut actual : Vec<(uint, uint, Rc<uint>)> =
      g.edges_from(1).collect();

    let mut expected : Vec<(uint, uint, Rc<uint>)> =
      vec!((1,1,Rc::new(0)),(1,2,Rc::new(1)),(1,3,Rc::new(2)));

    actual.sort();
    expected.sort();

    assert_eq!(actual, expected);
  }

  assert!(g.has_edges_from(1));
  assert!(g.has_edges_from(4));
  assert!(g.has_edges_to(1));
  assert!(g.has_edges_to(2));
  assert!(g.has_edges_to(3));
  assert!(!g.has_edges_from(2));
  assert!(!g.has_edges_to(4));
}

#[test]
fn test_tsort() {
  let mut g = Graph::new();

  for &x in [1,2,3,4,5].iter() {
    g.insert_vertex(x, x*2);
  }

  {
    g.insert_directed_edge(1,2,());
    g.insert_directed_edge(2,3,());
    g.insert_directed_edge(3,4,());
    g.insert_directed_edge(4,5,());

    let (a, b, c, d, e) = (2, 4, 6, 8, 10);

    let expected = Some(vec!((1, &a), (2, &b), (3, &c), (4, &d), (5, &e)));

    assert_eq!(g.topological_sort(), expected);
    assert!(g.is_acyclic());
  }

  g.clear_edges();

  {
    g.insert_directed_edge(5,4,());
    g.insert_directed_edge(4,3,());
    g.insert_directed_edge(3,2,());
    g.insert_directed_edge(2,1,());

    let (a, b, c, d, e) = (10, 8, 6, 4, 2);

    let expected = Some(vec!((5, &a), (4, &b), (3, &c), (2, &d), (1, &e)));

    assert_eq!(g.topological_sort(), expected);
    assert!(g.is_acyclic());
  }

  g.clear_edges();

  {
    g.insert_directed_edge(1,2,());
    g.insert_directed_edge(2,1,());

    assert_eq!(g.topological_sort(), None);
    assert!(!g.is_acyclic());
  }

  g.clear_edges();

  {
    g.insert_directed_edge(1,2,());
    g.insert_directed_edge(2,3,());
    g.insert_directed_edge(3,4,());
    g.insert_directed_edge(4,5,());
    g.insert_directed_edge(5,3,());

    assert!(!g.is_acyclic());
  }

  g.clear_edges();

  {
    g.insert_directed_edge(1,2,());
    g.insert_directed_edge(2,3,());
    g.insert_directed_edge(3,4,());
    g.insert_directed_edge(4,5,());
    g.insert_directed_edge(5,1,());

    assert!(!g.is_acyclic());
  }
}

#[test]
fn test_dfs_and_bfs() {
  let mut g = Graph::new();

  for &x in [1,2,3,4,5,6].iter() {
    g.insert_vertex(x, ());
  }

  g.insert_directed_edge(1,2,());
  g.insert_directed_edge(1,3,());
  g.insert_directed_edge(2,4,());
  g.insert_directed_edge(3,5,());

  //            1
  //          2   3
  //          4   5

  {
    let actual : Vec<uint> = g.dfs(1).map(|(x, &())| x).collect();
    let expected1 = vec!(1,3,5,2,4);
    let expected2 = vec!(1,2,4,3,5);
    assert!(actual == expected1 || actual == expected2);
  }

  {
    let actual : Vec<uint> = g.bfs(1).map(|(x, &())| x).collect();
    let expected1 = vec!(1,2,3,4,5);
    let expected2 = vec!(1,3,2,5,4);
    assert!(actual == expected1 || actual == expected2);
  }
}

#[test]
fn test_remove_vertex() {
  let mut g = Graph::new();

  for &x in [1,2,3,4,5].iter() {
    g.insert_vertex(x, ());
  }

  g.insert_directed_edge(3,1,());
  g.insert_directed_edge(2,3,());
  g.insert_directed_edge(1,5,());
  g.insert_directed_edge(5,2,());

  g.remove_vertex(3);

  assert_eq!(g.number_of_edges(), 2);
  assert_eq!(g.number_of_verticies(), 4);
}
