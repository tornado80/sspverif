use crate::types::Type;

use crate::smt::exprs::{smt_to_string, SmtExpr, SmtLet, SspSmtVar};

/**
* composition state smt gen helper type
*
* what do we need?
* - composition state sort name
* - composition state constructor name
* - composition state accessor names
* - composition state sort definition
* - composition state accessor helpers
* - overwrite/copy-on-write helper
*
* for that we need...
* - composition name
* - SmtPackageState values for each instance
*
*
   (declare-datatype State_right-pkey (
        (mk-state-right-pkey   (state-right-pkey-pk   (Array Int String))
                               (state-right-pkey-sk   (Array Int String))
                               (state-right-pkey-id   (Array String Int))
                               (state-right-pkey-ctr  Int)
                               (state-right-pkey-rand RandState))))
*
*/

pub struct SmtCompositionState<'a> {
    comp_name: &'a str,
    substate_names: Vec<&'a str>,
}

impl<'a> SmtCompositionState<'a> {
    pub fn new(comp_name: &'a str, substate_names: Vec<&'a str>) -> SmtCompositionState<'a> {
        SmtCompositionState {
            comp_name,
            substate_names,
        }
    }
    pub fn smt_sort(&self) -> SmtExpr {
        SmtExpr::Atom(format!("CompositionState-{}", self.comp_name))
    }

    pub fn smt_constructor(&self) -> SmtExpr {
        SmtExpr::Atom(format!("mk-composition-state-{}", self.comp_name))
    }

    pub fn smt_accessor(&self, inst_name: &str) -> SmtExpr {
        // TODO should we check that inst_name is in inst_names? same for SmtPackageState
        SmtExpr::Atom(format!(
            "composition-state-{}-{}",
            self.comp_name, inst_name
        ))
    }

    pub fn smt_access(&self, inst_name: &str, term: SmtExpr) -> SmtExpr {
        SmtExpr::List(vec![self.smt_accessor(inst_name), term])
    }

    pub fn smt_declare_datatype(&self) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for inst_name in &self.substate_names {
            let pkg_state = SmtPackageState {
                comp_name: self.comp_name,
                inst_name,
                state: vec![],
            };
            tmp.push(SmtExpr::List(vec![
                self.smt_accessor(inst_name),
                pkg_state.smt_sort(),
            ]))
        }

        SmtExpr::List(vec![
            SmtExpr::Atom("declare-datatype".to_string()),
            self.smt_sort(),
            SmtExpr::List(vec![SmtExpr::List(tmp)]),
        ])
    }

    pub fn smt_set(&self, target: &str, new: &SmtExpr, body: SmtExpr) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for inst_name in &self.substate_names {
            tmp.push(if *inst_name == target {
                new.clone()
            } else {
                self.smt_access(inst_name, SspSmtVar::GlobalState.into())
            });
        }

        SmtLet {
            bindings: vec![(smt_to_string(SspSmtVar::GlobalState), SmtExpr::List(tmp))],
            body,
        }
        .into()
    }
}

/**
 * packages state smt gen helper type
 *
 * what do we need?
 * - state type name ✅
 * - state type definition ✅
 * - state type constructor name ✅
 * - state type accessors ✅
 * - overwrite/copy-on-write helper ✅
 *
 * for that we need...
 * - composition name
 * - package instance name
 * - state variables
 */
pub struct SmtPackageState<'a> {
    comp_name: &'a str,
    inst_name: &'a str,
    state: Vec<(String, Type)>,
}

/**
 * comp = mod_prf_game
 * inst = multi_key
 */

impl<'a> SmtPackageState<'a> {
    pub fn new(
        comp_name: &'a str,
        inst_name: &'a str,
        state: Vec<(String, Type)>,
    ) -> SmtPackageState<'a> {
        SmtPackageState {
            comp_name,
            inst_name,
            state,
        }
    }

    pub fn smt_constructor(&self) -> SmtExpr {
        SmtExpr::Atom(format!("mk-state-{}-{}", self.comp_name, self.inst_name))
    }

    pub fn smt_sort(&self) -> SmtExpr {
        SmtExpr::Atom(format!("State_{}_{}", self.comp_name, self.inst_name))
    }

    pub fn smt_accessor(&self, id: &str) -> SmtExpr {
        SmtExpr::Atom(format!(
            "state-{}-{}-{}",
            self.comp_name, self.inst_name, id
        ))
    }

    pub fn smt_access(&self, id: &str, term: SmtExpr) -> SmtExpr {
        SmtExpr::List(vec![self.smt_accessor(id), term])
    }

    pub fn smt_declare_datatype(&self) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for (id, tipe) in &self.state {
            tmp.push(SmtExpr::List(vec![
                self.smt_accessor(id),
                tipe.clone().into(),
            ]))
        }

        SmtExpr::List(vec![
            SmtExpr::Atom("declare-datatype".to_string()),
            self.smt_sort(),
            SmtExpr::List(vec![SmtExpr::List(tmp)]),
        ])
    }

    pub fn smt_set(&self, id: &str, new: &SmtExpr) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for (varname, _) in self.state.clone() {
            if varname == *id {
                tmp.push(new.clone());
            } else {
                tmp.push(SmtExpr::List(vec![
                    self.smt_accessor(&varname),
                    SspSmtVar::SelfState.into(),
                ]));
            }
        }

        SmtExpr::List(tmp)
    }
}
