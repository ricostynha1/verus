//! 4-arm ablation switch for the `--counterexample` pipeline (B0 raw / B1
//! instantiate-only / B2 classify-only / B3 full pipeline — see
//! `CONTRIBUTION.md` §5b.2). Evaluation/paper-only, not a user-facing
//! feature: selected via the `VERUS_COUNTEREXAMPLE_ABLATION` env var
//! (unset/unrecognized = B3, the shipping default), never a CLI flag or
//! `Context` field, so it stays isolated from the normal `--counterexample`
//! path in every other file.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AblationArm {
    /// No instantiation, no classification (always REAL).
    B0,
    /// Instantiate, but skip Refute/Confirm (always REAL).
    B1,
    /// Skip instantiation; classify the raw Stage-1 witness.
    B2,
    /// Full pipeline (default): instantiate + classify.
    B3,
}

impl AblationArm {
    pub(crate) fn from_env() -> AblationArm {
        match std::env::var("VERUS_COUNTEREXAMPLE_ABLATION").ok().as_deref() {
            Some("B0") | Some("b0") => AblationArm::B0,
            Some("B1") | Some("b1") => AblationArm::B1,
            Some("B2") | Some("b2") => AblationArm::B2,
            _ => AblationArm::B3,
        }
    }

    pub(crate) fn instantiate(&self) -> bool {
        matches!(self, AblationArm::B1 | AblationArm::B3)
    }

    pub(crate) fn classify(&self) -> bool {
        matches!(self, AblationArm::B2 | AblationArm::B3)
    }

    pub(crate) fn label(&self) -> &'static str {
        match self {
            AblationArm::B0 => "B0 (raw: no instantiate, no classify)",
            AblationArm::B1 => "B1 (instantiate-only: no classify)",
            AblationArm::B2 => "B2 (classify-only: no instantiate)",
            AblationArm::B3 => "B3 (full pipeline: instantiate + classify)",
        }
    }
}
