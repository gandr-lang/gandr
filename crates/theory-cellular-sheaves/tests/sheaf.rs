//! A sheaf's construction and the gluing of a cover: the refusals of a
//! malformed map or section, and the verdict on agreeing and differing
//! sections.

use gandr_theory_cellular_sheaves::Agreement;
use gandr_theory_cellular_sheaves::CoverIndex;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Gluing;
use gandr_theory_cellular_sheaves::Obstruction;
use gandr_theory_cellular_sheaves::Sheaf;
use gandr_theory_cellular_sheaves::SheafError;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;

/// A set of points of a carrier of at most 64 points, one bit for each.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Points(u64);

impl Points
{
    /// The points of the set, lowest first.
    ///
    /// # Specification
    /// trivial.
    fn members(self) -> impl Iterator<Item = u32>
    {
        (0 .. 64_u32)
            .filter(move |&point| self.0.checked_shr(point).is_some_and(|rest| rest & 1 == 1))
    }
}

/// The sheaf of a face cover's site: its cells ordered by reverse
/// inclusion, so each cell lies below every smaller cell; each stalk one
/// value for each point; and each map keeping the values at the upper cell's
/// points.
///
/// # Specification
/// trivial.
fn site(cells: Vec<Points>) -> Sheaf<Points>
{
    let poset = GradedPoset::new(cells, |lower, upper| {
        if upper.0 & !lower.0 == 0 {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    })
    .expect("distinct sets of points");
    Sheaf::new(
        poset,
        |cell| Width::from(cell.members().count()),
        |lower, upper| {
            let lower = *lower;
            upper.members().map(move |point| {
                let place = lower
                    .members()
                    .take_while(|&member| member != point)
                    .count();
                Entry::from(place)
            })
        },
    )
    .expect("the face cover's sheaf")
}

/// The config shape's cover over `{host, port, tls}`, the points in that
/// order: the meet `{port}`, the face `addr = {host, port}` and the face
/// `secure = {port, tls}`, as cells 0, 1 and 2.
///
/// # Specification
/// trivial.
fn config() -> Sheaf<Points>
{
    site(vec![Points(0b010), Points(0b011), Points(0b110)])
}

#[test]
fn a_cover_glues_where_its_sections_agree_on_the_overlap()
{
    let sheaf = config();
    let (port, addr, secure) = (
        Element::from(0_usize),
        Element::from(1_usize),
        Element::from(2_usize),
    );
    assert_eq!(sheaf.width(port), Ok(Width::from(1_usize)));
    assert_eq!(sheaf.width(secure), Ok(Width::from(2_usize)));
    let past = Element::from(3_usize);
    assert_eq!(sheaf.width(past), Err(SheafError::CellOutside(past)));
    // `secure` holds its values at `port` and `tls`, and `addr` at `host` and
    // `port`. They agree at `port`.
    let agreeing: [(Element, &[u8]); 2] = [(secure, &[1, 0]), (addr, &[0, 1])];
    let Ok(Gluing::Glued(section)) = sheaf.glue(&agreeing)
    else {
        panic!("the two faces agree at their meet");
    };
    assert_eq!(section.at(port), Ok(&[1_u8][..]));
    assert_eq!(section.at(secure), Ok(&[1_u8, 0][..]));
    assert_eq!(section.at(addr), Ok(&[0_u8, 1][..]));
    let alone: [(Element, &[u8]); 1] = [(addr, &[0, 1])];
    let Ok(Gluing::Glued(section)) = sheaf.glue(&alone)
    else {
        panic!("one face glues alone");
    };
    assert_eq!(section.at(port), Ok(&[1_u8][..]));
    assert_eq!(section.at(secure), Err(SheafError::OutsideSupport(secure)));
    // They differ at `port`: the refusal names the meet and its one entry.
    let parting: [(Element, &[u8]); 2] = [(secure, &[1, 0]), (addr, &[0, 0])];
    assert_eq!(
        sheaf.glue(&parting),
        Ok(Gluing::Obstructed(vec![Obstruction {
            members: (CoverIndex::from(0_usize), CoverIndex::from(1_usize)),
            overlap: port,
            entry: Entry::from(0_usize),
        }]))
    );
    // The pair alone, as a caller that changed one member compares it.
    assert_eq!(
        sheaf.compare(agreeing[0], agreeing[1]),
        Ok(Agreement::Agree)
    );
    assert_eq!(
        sheaf.compare(parting[0], parting[1]),
        Ok(Agreement::Differ {
            overlap: port,
            entry: Entry::from(0_usize),
        })
    );
}

#[test]
fn a_section_of_another_width_is_refused()
{
    let sheaf = config();
    let secure = Element::from(2_usize);
    let short: [(Element, &[u8]); 1] = [(secure, &[1])];
    assert_eq!(
        sheaf.glue(&short),
        Err(SheafError::SectionWidth {
            cell: secure,
            width: Width::from(1_usize),
        })
    );
    let full: (Element, &[u8]) = (Element::from(1_usize), &[0, 1]);
    assert_eq!(
        sheaf.compare(full, short[0]),
        Err(SheafError::SectionWidth {
            cell: secure,
            width: Width::from(1_usize),
        })
    );
}

/// A cell of a chain, by its place in the chain.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
struct Link(usize);

/// The chain of `count` cells, each below every later one.
///
/// # Specification
/// trivial.
fn chain(count: ElementCount) -> GradedPoset<Link>
{
    GradedPoset::new(
        (0 .. usize::from(count)).map(Link).collect(),
        |lower, upper| {
            if lower < upper {
                Comparison::Below
            }
            else {
                Comparison::NotBelow
            }
        },
    )
    .expect("a chain")
}

#[test]
fn a_map_past_its_stalk_is_refused()
{
    let refused = Sheaf::new(
        chain(ElementCount::from(2_usize)),
        |_| Width::from(1_usize),
        |_, _| [Entry::from(1_usize)],
    );
    assert_eq!(
        refused.map(|_| ()),
        Err(SheafError::EntryOutside {
            lower: Element::from(0_usize),
            upper: Element::from(1_usize),
            entry: Entry::from(1_usize),
        })
    );
}

#[test]
fn a_map_of_another_width_is_refused()
{
    let refused = Sheaf::new(
        chain(ElementCount::from(2_usize)),
        |_| Width::from(1_usize),
        |_, _| [],
    );
    assert_eq!(
        refused.map(|_| ()),
        Err(SheafError::RestrictionWidth {
            lower: Element::from(0_usize),
            upper: Element::from(1_usize),
            width: Width::from(0_usize),
        })
    );
}

#[test]
fn a_map_that_does_not_compose_is_refused()
{
    // Each map keeps both entries in place, but the map from the lowest cell
    // to the highest swaps them, so it differs from the map through the
    // middle at the first entry.
    let refused = Sheaf::new(
        chain(ElementCount::from(3_usize)),
        |_| Width::from(2_usize),
        |&lower, &upper| {
            if (lower, upper) == (Link(0), Link(2)) {
                [Entry::from(1_usize), Entry::from(0_usize)]
            }
            else {
                [Entry::from(0_usize), Entry::from(1_usize)]
            }
        },
    );
    assert_eq!(
        refused.map(|_| ()),
        Err(SheafError::NotFunctorial {
            lower: Element::from(0_usize),
            middle: Element::from(1_usize),
            upper: Element::from(2_usize),
            entry: Entry::from(0_usize),
        })
    );
}

/// A cell of two points joined by two edges.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Bigon
{
    /// One of the two points.
    Point(usize),
    /// One of the two edges, each above both points.
    Edge(usize),
}

#[test]
fn an_overlap_with_two_least_cells_compares_at_each()
{
    // The two points overlap at both edges, and neither edge lies below the
    // other. Each point's stalk has two entries; the first edge reads the
    // first entry of each, and the second edge the second.
    let cells = vec![
        Bigon::Point(0),
        Bigon::Point(1),
        Bigon::Edge(0),
        Bigon::Edge(1),
    ];
    let poset = GradedPoset::new(cells, |lower, upper| match (*lower, *upper) {
        (Bigon::Point(_), Bigon::Edge(_)) => Comparison::Below,
        (Bigon::Point(_) | Bigon::Edge(_), Bigon::Point(_) | Bigon::Edge(_)) => {
            Comparison::NotBelow
        },
    })
    .expect("a bigon");
    let sheaf = Sheaf::new(
        poset,
        |cell| match *cell {
            Bigon::Point(_) => Width::from(2_usize),
            Bigon::Edge(_) => Width::from(1_usize),
        },
        |_, upper| match *upper {
            Bigon::Edge(edge) | Bigon::Point(edge) => [Entry::from(edge)],
        },
    )
    .expect("the bigon's sheaf");
    let (first, second) = (Element::from(0_usize), Element::from(1_usize));
    // The two sections agree on the first edge and differ on the second.
    let parting: [(Element, &[u8]); 2] = [(first, &[1, 1]), (second, &[1, 0])];
    assert_eq!(
        sheaf.glue(&parting),
        Ok(Gluing::Obstructed(vec![Obstruction {
            members: (CoverIndex::from(0_usize), CoverIndex::from(1_usize)),
            overlap: Element::from(3_usize),
            entry: Entry::from(0_usize),
        }]))
    );
    let agreeing: [(Element, &[u8]); 2] = [(first, &[1, 0]), (second, &[1, 0])];
    assert!(
        matches!(sheaf.glue(&agreeing), Ok(Gluing::Glued(_))),
        "sections that agree on both edges glue"
    );
}
