use std::io::{Result, Write};
#[allow(non_snake_case)]
pub fn declare_datatype_Maybe(t: &str) {
    println!(
        "(declare-datatype Maybe_{0} (
        (mk-none-{0})
        (mk-some-{0} (some-{0}-get {0}))
    ))",
        t
    );
}

#[allow(non_snake_case)]
pub fn declare_par_Maybe<W: Write>(w: &mut W) -> Result<()> {
    write!(
        w,
        "(declare-datatypes ((Maybe 1)) ((par (T) ((mk-some (maybe-get T)) (mk-none)))))"
    )
}


#[allow(non_snake_case)]
pub fn declare_Empty<W: Write>(w: &mut W) -> Result<()> {
    write!(
        w,
        "(declare-datatype Empty (mk-empty))"
    )
}



#[allow(non_snake_case)]
pub fn declare_datatype_Tuple<W: Write>(w: &mut W, ts: &[&str]) -> Result<()> {
    let mut out = String::new();
    out.push_str(&format!("(declare-datatype Tuple__{}", ts.join("_")));
    out.push_str(&format!("((mk-tuple-{}", ts.join("-")));
    for (i, t) in ts.iter().enumerate() {
        out.push_str(&format!("(tuple-get-{} {})", i, t));
    }
    out.push_str(")))");

    write!(w, "{}", out)
}

#[allow(non_snake_case)]
pub fn declare_Tuple<W: Write>(w: &mut W, n: usize) -> Result<()> {
    let types: String = (1..n + 1)
        .map(|i| format!("T{}", i))
        .fold(String::new(), |acc, v| {
            let mut acc = acc;
            acc.push(' ');
            acc.push_str(&v);
            acc
        });
    let ds: String =
        (1..n + 1)
            .map(|i| format!("(el{0} T{0})", i))
            .fold(String::new(), |acc, v| {
                let mut acc = acc;
                acc.push(' ');
                acc.push_str(&v);
                acc
            });

    write!(
        w,
        "(declare-datatypes ((Tuple{0} {0})) (
        (par ({1}) ((mk-tuple{0} {2})
        ))))",
        n, types, ds
    )
}

pub fn declare_tuples<W: Write>(w: &mut W, n: usize) -> Result<()> {
    for i in 1..n {
        declare_Tuple(w, i)?;
    }

    Ok(())
}
