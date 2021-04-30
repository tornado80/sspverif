trait Type {}

#[derive(Debug)]
struct BasicType(String);

impl Type for BasicType {}

trait Expression {}

#[derive(Debug)]
struct Identifier {
    name: String,
}

impl Expression for Identifier {}

#[derive(Debug)]
struct FnInvoc<ArgsT: Expression, RetT: Type> {
    name: String,
    args: ArgsT,
    ret_tipe: RetT,
}

impl<Args: Expression, RetT: Type> Expression for FnInvoc<Args, RetT> {}

#[derive(Debug)]
struct Literal<T: Type> {
    value: String,
    tipe: T,
}

impl<T: Type> Expression for Literal<T> {}

#[derive(Debug)]
struct Pair<LeftT: Expression, RightT: Expression> {
    left: LeftT,
    right: RightT,
}

impl<LeftT: Expression, RightT: Expression> Expression for Pair<LeftT, RightT> {}

#[derive(Debug)]
enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

#[derive(Debug)]
struct Arith<LeftT: Expression, RightT: Expression> {
    op: ArithOp,
    left: LeftT,
    right: RightT,
}

impl<LeftT: Expression, RightT: Expression> Expression for Arith<LeftT, RightT> {}

fn main() {
    let expr = Arith {
        op: ArithOp::Add,
        left: FnInvoc {
            name: "f".to_string(),
            args: Pair {
                left: Identifier {
                    name: "k".to_string(),
                },
                right: Literal {
                    value: "\"t0ps3cr3t\"".to_string(),
                    tipe: BasicType("String".to_string()),
                },
            },
            ret_tipe: BasicType("String".to_string()),
        },
        right: Identifier {
            name: "0xabc".to_string(),
        },
    };

    println!("{:?}", expr);
}
