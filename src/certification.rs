pub trait WitnessBuilder {
    type Tree;

    fn empty() -> Self::Tree;
    fn fork(l: Self::Tree, r: Self::Tree) -> Self::Tree;
    fn node(label: &[u8], child: Self::Tree) -> Self::Tree;
    fn leaf(bytes: &[u8]) -> Self::Tree;
    fn pruned(hash: [u8; 32]) -> Self::Tree;
}
