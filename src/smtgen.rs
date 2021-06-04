

/*

Bigger Story
============

We have a Type/Sort/Datastructuure with all variable (names) in that scope.

The set_value code will advance one step and *copy* all variables from the old Datastructure to the new one apart from the one we have just written.

If/Then/Else via hirarchial counters.

For if-then-else we have a different stucture/sorty/type inside the ite then outside so for each branch at the end we need to filter and generate the correct "outer" structure

returns/aborts inside (as opposed to just one at the very end) are still a big headache

*/






fn set_value(identifier: Identifier, expression: Expression, varname: String, ctr: i32, scope: Scope) {
    let mut result = String::new();
    result.push(format!("(let (({varname}.{ctr} (make-variable-mapping",
                        varname=varname, ctr=ctr));

    for ident in scope.all() {
        if ident != identifier {
            println!("(access-variable-mapping-at-{ident} variablemapping{ctr-1})")
        } else {
            println!("({:?})", expression)
        }
        println!(")");
    }
    println!(")))");
}


pub fn generate_smt(block: &Vec<Box<Statement>>, varname:String) -> () {
    let mut ctr:i32 = 1;
    let mut scope = Scope::new();

    type_inference(block, scope);

    for stmt in block {
        match &**stmt {
            Statement::Abort => {

            },
            Statement::Return(expr) => {

            },
            Statement::Assign(id, expr) => {
                set_value(id, expr, varname, ctr, scope);
            },
            Statement::TableAssign(id, idx, expr) => {

            },
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                varnameif = "{varname}.{ctr}.if";
                let ifsmt = generate_smt(ifcode, varnameif);
                varnameelse = "{varname}.{ctr}.else";
                let elsesmt = generate_smt(elsecode, varnameelse);
                "(let (({varname}.{ctr} (scope-adapt (ite {expr} ({ifsmt}) ({elsesmt})))))"
            }
        }
        ctr = ctr + 1;
    }
    for i in 1..ctr {
        println!(")");
    }
}
