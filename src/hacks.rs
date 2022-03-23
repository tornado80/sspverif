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

pub fn declare_par_Maybe() {
    println!("(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))");
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

pub fn declare_Tuple(n: usize) {
    let types: String = (1..n + 1)
        .map(|i| format!("T{}", i))
        .fold(String::new(), |acc, v| {
            let mut acc = acc.clone();
            acc.push_str(" ");
            acc.push_str(&v);
            acc
        });
    let ds: String =
        (1..n + 1)
            .map(|i| format!("(el{0} T{0})", i))
            .fold(String::new(), |acc, v| {
                let mut acc = acc.clone();
                acc.push_str(" ");
                acc.push_str(&v);
                acc
            });

    let decl = format!(
        "(declare-datatypes ((Tuple{0} {0})) (
        (par ({1}) ((mk-tuple{0} {2})
        ))))",
        n, types, ds
    );

    println!("{}", decl)
}

pub fn declare_tuples(n: usize) {
    for i in 1..n {
        declare_Tuple(i);
    }
}
