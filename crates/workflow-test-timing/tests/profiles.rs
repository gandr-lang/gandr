//! The repository's nextest profiles, read from `.config/nextest.toml`: the
//! local gate ends a test only where CI does, so a loaded host lengthens a
//! gate and never fails it (#3912).

/// The local `default` profile and the `ci` profile mark a test slow at the
/// same period and end it only past five minutes, a hang. A local profile that
/// ended a test sooner would fail a gate on a loaded host that CI passes.
#[test]
fn the_local_gate_ends_a_test_only_where_ci_does_3912()
{
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.config/nextest.toml");
    let text = std::fs::read_to_string(&path).expect("the repository's nextest config reads");
    let config: toml::Table = text.parse().expect("the nextest config is TOML");
    let ends_after = |profile: &str| {
        let timeout = config
            .get("profile")
            .and_then(|profiles| profiles.get(profile))
            .and_then(|table| table.get("slow-timeout"))
            .unwrap_or_else(|| panic!("`{profile}` states a slow-timeout"));
        let period = timeout
            .get("period")
            .and_then(toml::Value::as_str)
            .and_then(|period| period.strip_suffix('s'))
            .and_then(|seconds| seconds.parse::<i64>().ok())
            .unwrap_or_else(|| panic!("`{profile}`'s period is a count of seconds"));
        let terminate = timeout
            .get("terminate-after")
            .and_then(toml::Value::as_integer)
            .unwrap_or_else(|| panic!("`{profile}` ends a hang"));
        (period, period.saturating_mul(terminate))
    };
    assert_eq!(
        ends_after("ci"),
        (30, 300),
        "CI marks a test slow at 30 s and ends it at 5 min"
    );
    assert_eq!(
        ends_after("default"),
        ends_after("ci"),
        "the local gate marks and ends a test where CI does"
    );
}
