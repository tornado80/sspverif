trait Type: Clone {}

#[derive(Debug, Clone)]
struct BasicType(String);

impl Type for BasicType {}

trait Expression: Clone {}

#[derive(Debug, Clone)]
struct Identifier (String);

impl Expression for Identifier {}

#[derive(Debug, Clone)]
struct FnCall<ArgsT: Expression, RetT: Type> {
    name: String,
    args: ArgsT,
    ret_tipe: RetT,
}

impl<Args: Expression, RetT: Type> Expression for FnCall<Args, RetT> {}

#[derive(Debug, Clone)]
struct OracleInvoc<ArgsT: Expression, RetT: Type> {
    name: String,
    args: ArgsT,
    ret_tipe: RetT,
}

impl<Args: Expression, RetT: Type> Expression for OracleInvoc<Args, RetT> {}

#[derive(Debug, Clone)]
struct Literal<T: Type> {
    value: String,
    tipe: T,
}

impl<T: Type> Expression for Literal<T> {}

#[derive(Debug, Clone)]
struct Pair<LeftT: Expression, RightT: Expression> {
    left: LeftT,
    right: RightT,
}

impl<LeftT: Expression, RightT: Expression> Expression for Pair<LeftT, RightT> {}

#[derive(Debug, Clone)]
enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

#[derive(Debug, Clone)]
struct Arith<LeftT: Expression, RightT: Expression> {
    op: ArithOp,
    left: LeftT,
    right: RightT,
}

impl<LeftT: Expression, RightT: Expression> Expression for Arith<LeftT, RightT> {}

trait Statement: Clone {
    type Next;

    fn next_stmt(&self) -> Option<Self::Next>;
}

#[derive(Debug, Clone)]
struct Assign<Expr: Expression, Next: Statement> {
    ident: Identifier,
    val: Expr,
    next: Next,
}

impl<Expr:Expression, Next: Statement> Statement for Assign<Expr, Next> {
    type Next = Next;

    fn next_stmt(&self) -> Option<Next> {
        Some(self.next.clone())
    }
}

#[derive(Debug, Clone)]
enum Term{}

#[derive(Debug, Clone)]
struct BlockEnd();

impl Statement for BlockEnd {
    type Next = Term; 

    fn next_stmt(&self) -> Option<Term> {
        None
    }
}

#[derive(Debug, Clone)]
struct Return<Expr: Expression>(Expr);

impl<Expr: Expression> Statement for Return<Expr> {
    type Next = BlockEnd; 

    fn next_stmt(&self) -> Option<BlockEnd> {
        Some(BlockEnd())
    }
}

#[derive(Debug, Clone)]
struct Abort(i32);

impl Statement for Abort {
    type Next = BlockEnd; 

    fn next_stmt(&self) -> Option<BlockEnd> {
        Some(BlockEnd())
    }
}

#[derive(Debug, Clone)]
struct IfThenElse<Cond: Expression, Then: Statement, Else: Statement, Next: Statement> {
    cond: Cond,
    then: Then,
    elze: Else,
    next: Next,
}

impl<Cond: Expression, Then: Statement, Else: Statement, Next: Statement> Statement for IfThenElse<Cond,Then,Else,Next> {
    type Next = Next;

    fn next_stmt(&self) -> Option<Next> {
        Some(self.next.clone())
    }
}
/*
 *
 * if foo:
 *      x <- 23
 * else:
 *      x <- 42
 * return x
 *
 * */

fn main() {
    let expr = Arith {
        op: ArithOp::Add,
        left: FnCall {
            name: "f".to_string(),
            args: Pair {
                left: Identifier("k".to_string()),
                right: Literal {
                    value: "\"t0ps3cr3t\"".to_string(),
                    tipe: BasicType("String".to_string()),
                },
            },
            ret_tipe: BasicType("String".to_string()),
        },
        right: Identifier("0xabc".to_string()),
    };

    let assign = Assign{
        ident: Identifier("x".to_string()),
        val: expr,
        next: BlockEnd(),
    };


    println!("{:?}", assign);
}
