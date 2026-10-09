//! The flat regular-expression layout: a nested expression reads back node
//! for node as it was built.

use gandr_surface_grammar::Regex;
use gandr_surface_grammar::RegexShape;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::Sym;
use gandr_surface_grammar::Tile;
use gandr_surface_grammar::TileLabel;

#[test]
fn nested_shapes_read_back_as_built()
{
    let branch_hole = Regex::sort(Sort::Expression);
    let branch_tail = Regex::seq([Regex::tile(TileLabel("b")), Regex::empty()]);
    let regex = Regex::seq([
        Regex::tile(TileLabel("a")),
        Regex::alt([branch_hole.clone(), branch_tail.clone()]),
        Regex::optional(Regex::repeat(Regex::tile(TileLabel("c")))),
        Regex::seq([]),
    ]);

    let RegexShape::Seq(items) = regex.view().shape()
    else {
        panic!("the root is a sequence");
    };
    let &[first, second, third, fourth] = items.as_slice()
    else {
        panic!("the sequence has four items: {items:?}");
    };

    assert_eq!(
        RegexShape::Sym(Sym::Tile(Tile::new(TileLabel("a")))),
        first.shape()
    );

    let RegexShape::Alt(branches) = second.shape()
    else {
        panic!("the second item is an alternation");
    };
    let rebuilt: Vec<Regex> = branches.iter().map(|branch| branch.to_regex()).collect();
    assert_eq!(vec![branch_hole, branch_tail], rebuilt);

    let RegexShape::Optional(optional) = third.shape()
    else {
        panic!("the third item is optional");
    };
    let RegexShape::Repeat(repeated) = optional.shape()
    else {
        panic!("the optional wraps a repetition");
    };
    assert_eq!(
        RegexShape::Sym(Sym::Tile(Tile::new(TileLabel("c")))),
        repeated.shape()
    );

    assert_eq!(RegexShape::Seq(Vec::new()), fourth.shape());
}
