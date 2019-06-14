use rs_graph::*;



#[cfg(test)]
mod tests {
    use rs_graph::*;
    use rs_graph::traits::Directed;

    #[test]
    fn test_new() {

        let mut g = LinkedListGraph::<u32>::default();
        let nodes = g.add_nodes(6);
        g.add_edge(nodes[0], nodes[1]);
        g.add_edge(nodes[1], nodes[0]);
        g.add_edge(nodes[1], nodes[2]);
        g.add_edge(nodes[0], nodes[3]);
        g.add_edge(nodes[3], nodes[2]);

       //example use of outgoing edges
        g.outedges(nodes[0]).for_each( |(_e, n ) | println!( "{:?}", n) );

    }
}