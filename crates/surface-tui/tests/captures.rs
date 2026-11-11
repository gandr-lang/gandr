//! The rendered captures: the recorded bus frames of each scene, replayed
//! through the side view. Each state that a frame leaves keeps every rule of
//! the visual language. A blank line in the frames ends a capture: the scene's
//! panes are drawn as SVG and compared with the committed file.
//! `UPDATE_EXPECT=1` records the files again.

use std::fs;
use std::path::Path;

use expect_test::expect_file;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_render_remote::Shown;
use gandr_surface_render_remote::conform;
use gandr_surface_tui::Following;
use gandr_surface_tui::rendering;
use gandr_surface_tui::svg;

/// A scene: the stem of its frames and of its captures, and the first head of
/// each pane that it shows, in order.
#[derive(Clone, Copy, Debug)]
struct Scene
{
    /// The stem of the files.
    stem: &'static str,
    /// The first head of each pane of the run that the capture shows.
    leads: &'static [&'static str],
}

/// Replay the frames of `scene` through the side view, check each state that a
/// frame leaves against the rules, and compare each capture with its file.
///
/// # Specification
/// - requires: `tests/frames/<stem>.jsonl` holds one frame per line, and a
///   blank line after each state that the scene captures.
/// - ensures: each frame leaves a rendering that breaks no rule, with the state
///   before it as the earlier one. The capture at the n-th blank line,
///   one-based, equals `tests/captures/<stem>.<n>.svg`, and the scene has one
///   capture at least.
/// - provides: the golden of each capture of the scene.
/// - fails: never.
/// - panics: when a file is missing, a line is not a frame, a state breaks a
///   rule, or a capture differs from its file.
/// - executable: none — the effects are the files that the comparison reads,
///   and the panics are the checks.
///
/// # Adequacy
/// - hypothesis: L3 — the recorded frames give the committed SVG; a change of
///   one column's width fails the comparison with the lines that moved.
/// - witness: `tests::captures::the_warrants_scene_renders_as_its_captures`
/// - witness: `tests::captures::the_schedule_scene_renders_as_its_capture`
fn captured(scene: Scene)
{
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let frames = fs::read_to_string(
        tests
            .join("frames")
            .join(scene.stem)
            .with_extension("jsonl"),
    )
    .expect("the scene's frames are committed");
    let captures = tests.join("captures");
    let mut following = Following::default();
    let mut earlier = following.frame();
    let mut drawn = rendering(&earlier);
    let mut taken = 0_usize;
    for (number, line) in frames.lines().enumerate() {
        if line.is_empty() {
            taken = taken.saturating_add(1);
            let shown = drawn
                .panes
                .windows(scene.leads.len())
                .find(|run| {
                    run.iter().zip(scene.leads).all(|(pane, &lead)| {
                        pane.heads
                            .first()
                            .is_some_and(|head| <&str>::from(head.name) == lead)
                    })
                })
                .unwrap_or_default();
            assert!(
                !shown.is_empty(),
                "capture {taken} of {} shows its panes",
                scene.stem
            );
            expect_file![captures.join(format!("{}.{taken}.svg", scene.stem))]
                .assert_eq(&svg(shown));
            continue;
        }
        let frame: RenderFrame = serde_json::from_str(line).expect("each line is a frame");
        let _heard = following.hear(&frame);
        let now = following.frame();
        let next = rendering(&now);
        let breaches = conform(&Shown {
            frame: &now,
            rendering: &next,
            before: Some((&earlier, &drawn)),
        });
        assert_eq!(
            breaches,
            [],
            "line {} of {} keeps every rule",
            number.saturating_add(1),
            scene.stem
        );
        earlier = now;
        drawn = next;
    }
    assert!(taken > 0, "{} captures a state", scene.stem);
}

/// The warrants scene: the account pane of one source, after an edit breaks
/// one declaration, after the edit that repairs it, and after the kernel
/// admits it.
#[test]
fn the_warrants_scene_renders_as_its_captures()
{
    captured(Scene {
        stem: "warrants",
        leads: &["declaration"],
    });
}

/// The schedule scene: the activity pane of the hub's pool while the toolset
/// checks the corpus, one row per core and the totals.
#[test]
fn the_schedule_scene_renders_as_its_capture()
{
    captured(Scene {
        stem: "schedule",
        leads: &["world", "cores"],
    });
}

/// The stack scene: the stack pane at the editor's cursor in a nested call,
/// at a hole three spines deep and after the cursor moves out to the middle
/// spine.
#[test]
fn the_stack_scene_renders_as_its_captures()
{
    captured(Scene {
        stem: "stack",
        leads: &["head"],
    });
}
