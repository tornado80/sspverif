use crate::expressions::Expression;
use crate::identifier::pkg_ident::{
    PackageConstIdentifier, PackageIdentifier, PackageStateIdentifier,
};
use crate::identifier::Identifier;
use crate::package::{Composition, Package, PackageInstance};
use crate::proof::GameInstance;
use crate::split::SplitPath;
use crate::writers::smt::partials::PartialsDatatype;
use crate::writers::smt::patterns::pkg_consts::PackageConstsPattern;
use crate::writers::smt::patterns::{declare_datatype, PackageStateSelector};
use crate::writers::smt::{
    contexts::{GameInstanceContext, OracleContext, PackageInstanceContext, SplitOracleContext},
    exprs::SmtExpr,
    patterns::{DatastructurePattern, PackageStatePattern},
};

impl<'a> PackageInstanceContext<'a> {
    pub(crate) fn game_inst_ctx(&self) -> GameInstanceContext<'a> {
        self.game_ctx.clone()
    }

    pub(crate) fn game_inst(&self) -> &'a GameInstance {
        self.game_ctx.game_inst
    }

    pub(crate) fn game(&self) -> &'a Composition {
        self.game_inst().game()
    }

    pub(crate) fn split_oracle_ctx_by_name(
        &self,
        oracle_name: &str,
        partials: &'a PartialsDatatype,
    ) -> Option<SplitOracleContext<'a>> {
        let inst_offs = self.inst_offs;
        let inst = &self.game().pkgs[inst_offs];
        let split_oracle_offs = inst
            .pkg
            .split_oracles
            .iter()
            .position(|odef| odef.sig.name == oracle_name)?;

        Some(SplitOracleContext {
            game_inst_context: self.game_ctx.clone(),
            pkg_inst_offs: inst_offs,
            split_oracle_offs,
            partials,
        })
    }

    pub(crate) fn oracle_ctx_by_name(&self, oracle_name: &str) -> Option<OracleContext<'a>> {
        let inst_offs = self.inst_offs;
        let inst = &self.game().pkgs[inst_offs];
        let oracle_offs = inst
            .pkg
            .oracles
            .iter()
            .position(|odef| odef.sig.name == oracle_name)?;

        Some(OracleContext {
            game_inst_context: self.game_ctx.clone(),
            pkg_inst_offs: inst_offs,
            oracle_offs,
        })
    }

    pub(crate) fn split_oracle_ctx_by_name_and_path(
        &self,
        oracle_name: &str,
        oracle_path: &SplitPath,
        partials: &'a PartialsDatatype,
    ) -> Option<SplitOracleContext<'a>> {
        let inst_offs = self.inst_offs;
        let inst = &self.game().pkgs[inst_offs];
        let split_oracle_offs = inst
            .pkg
            .split_oracles
            .iter()
            .position(|odef| odef.sig.name == oracle_name && &odef.sig.path == oracle_path)?;

        Some(SplitOracleContext {
            game_inst_context: self.game_ctx.clone(),
            pkg_inst_offs: inst_offs,
            split_oracle_offs,
            partials,
        })
    }

    pub(crate) fn oracle_ctx_by_oracle_offs(
        &self,
        oracle_offs: usize,
    ) -> Option<OracleContext<'a>> {
        let oracle_count = self.game().pkgs[self.inst_offs].pkg.oracles.len();
        if oracle_offs >= oracle_count {
            return None;
        }

        let game_ctx = self.game_ctx.clone();
        let inst_offs = self.inst_offs;

        Some(OracleContext {
            game_inst_context: game_ctx,
            pkg_inst_offs: inst_offs,
            oracle_offs,
        })
    }

    pub(crate) fn pkg_inst(&self) -> &'a PackageInstance {
        &self.game().pkgs[self.inst_offs]
    }

    pub(crate) fn pkg(&self) -> &'a Package {
        &self.pkg_inst().pkg
    }

    pub(crate) fn pkg_inst_name(&self) -> &'a str {
        &self.pkg_inst().name
    }

    pub(crate) fn pkg_name(&self) -> &'a str {
        &self.pkg().name
    }

    pub(crate) fn pkg_params(&self) -> &'a [(PackageConstIdentifier, Expression)] {
        &self.pkg_inst().params
    }

    pub(crate) fn pkg_consts_pattern(&self) -> PackageConstsPattern<'a> {
        PackageConstsPattern {
            pkg_name: &self.pkg_inst().pkg.name,
        }
    }

    pub(crate) fn pkg_state_pattern(&self) -> PackageStatePattern<'a> {
        let pkg_name = &self.pkg_inst().pkg.name;

        let params = &self.pkg_inst().params;

        PackageStatePattern { pkg_name, params }
    }

    pub(crate) fn smt_declare_pkg_consts(&self) -> SmtExpr {
        let pkg = &self.pkg_inst().pkg;
        let pattern = self.pkg_consts_pattern();
        let spec = pattern.datastructure_spec(pkg);

        declare_datatype(&pattern, &spec)
    }

    pub(crate) fn smt_declare_pkgstate(&self) -> SmtExpr {
        let pkg = &self.pkg_inst().pkg;
        let pattern = self.pkg_state_pattern();
        let spec = pattern.datastructure_spec(pkg);

        declare_datatype(&pattern, &spec)
    }

    pub(crate) fn smt_access_pkgstate<S: Into<SmtExpr>>(
        &self,
        pkg_state: S,
        field_name: &str,
    ) -> Option<SmtExpr> {
        let pkg = &self.game().pkgs[self.inst_offs].pkg;

        let pkg_state_pattern = self.pkg_state_pattern();
        let pkg_state_spec = pkg_state_pattern.datastructure_spec(pkg);
        let pkg_state_field = self.field_selector(field_name)?;

        pkg_state_pattern.access(&pkg_state_spec, &pkg_state_field, pkg_state)
    }

    fn field_selector(&self, field_name: &'a str) -> Option<PackageStateSelector<'a>> {
        let pkg_inst = &self.game().pkgs[self.inst_offs];

        // return none if no field with that name exists
        let (_, tipe, _) = pkg_inst
            .pkg
            .state
            .iter()
            .find(|(name, _tipe, _file_pos)| name == field_name)?;

        Some(PackageStateSelector {
            name: field_name,
            ty: tipe,
        })
    }

    pub(crate) fn smt_update_pkgstate_from_locals(&self) -> Option<SmtExpr> {
        let game = self.game();
        let game_inst = self.game_inst();
        let pkg_inst = &game.pkgs[self.inst_offs];
        let pkg = &pkg_inst.pkg;
        let pkg_name = &pkg.name;

        let pkg_state_pattern = self.pkg_state_pattern();
        let pkg_state_spec = pkg_state_pattern.datastructure_spec(pkg);

        pkg_state_pattern.call_constructor(&pkg_state_spec, &(), |sel| {
            let PackageStateSelector { name, ty } = *sel;
            Some(
                Identifier::PackageIdentifier(PackageIdentifier::State(PackageStateIdentifier {
                    pkg_name: pkg_name.clone(),
                    name: name.to_string(),
                    tipe: ty.clone(),
                    pkg_inst_name: Some(pkg_inst.name.clone()),
                    game_name: Some(game.name.clone()),
                    game_inst_name: Some(game_inst.name.clone()),
                    proof_name: None,
                }))
                .into(),
            )
        })
    }
}
