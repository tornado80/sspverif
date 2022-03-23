pub fn declare_datatype_Maybe(t: &str) {
    println!(
        "(declare-datatype Maybe_{0} (
        (mk-some-{0} (some-{0}-get {0}))
        (mk-none-{0})
    ))",
        t
    );
}
