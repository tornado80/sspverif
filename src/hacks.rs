use crate::types::Type;

pub fn declare_datatype_Maybe(t: &str) {
    println!(
        "(declare-datatype Maybe_{0} (
        (mk-some-{0} (some-{0}-get {0}))
        (mk-none-{0})
    ))",
        t
    );
}

pub fn declare_datatype_Tuple(ts: &[&str]) {
    let mut out = String::new();
    out.push_str(&format!("(declare-datatype Tuple__{}", ts.join("_")));
    out.push_str(&format!("((mk-tuple-{}", ts.join("-")));
    for (i, t) in ts.iter().enumerate() {
        out.push_str(&format!("(tuple-get-{} {})", i, t));
    }
    out.push_str(")))");

    println!("{}", out);
}
