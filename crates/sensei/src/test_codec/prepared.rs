//! Shared prepared target and per-call serial execution for unit tests.

pub(crate) fn execution() -> crate::native::worker::Execution<'static> {
    crate::native::worker::Execution::new(
        &udon::exec::SerialExecutor,
        udon::exec::TaskBudget::SERIAL,
    )
}
pub(crate) fn target() -> &'static crate::native::target::FixedTarget {
    static TARGET: std::sync::LazyLock<crate::native::target::FixedTarget> =
        std::sync::LazyLock::new(|| {
            crate::native::target::FixedTarget::build(
                crate::native::srs::PreparedSrs::shared(),
                execution(),
            )
            .unwrap()
        });
    &TARGET
}
