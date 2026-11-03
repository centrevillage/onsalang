//! The receivers of the methods of the sequences (§5.3, S-853): the notes
//! of the E0416 of an element that does not meet a bound of std's `impl`
//! of them (`std/core/seq.onsa`).

use super::*;

/// The forms that need no Dup or Copy element (S-853).
const IN_PLACE: &str = "to use the elements as they are, borrow one by its index (`xs[i]`), take them out with `for x in move xs`, set each in a `for` loop, make the array with `array.from_fn`, or copy each element with its own `copy_from!` (§5.3, §5.2)";

impl<'a> Checker<'a> {
    /// The E0416 `d` of the element `elem`, shown as `shown`, that does not
    /// meet `bound`: of `Dup` and `Copy` its kind and the forms that need
    /// neither; of a number trait, that it meets none (§6.3). No candidate.
    pub(crate) fn seq_element_notes(&self, d: Diagnostic, elem: TyId, shown: &str, bound: Bound) -> Diagnostic {
        if !matches!(bound, Bound::Dup | Bound::Copy) {
            return d.with_rule(format!(
                "`{shown}` meets no number trait (`{}`, §6.3); the numbers are the integer and float types",
                bound.name()
            ));
        }
        let b = self.bounds();
        // A type parameter is of the kind its bounds say and no more (§4.5):
        // with the implicit `Dup` it may be Shared, with `?Dup` Affine.
        if matches!(self.ty(elem), Ty::Param(_)) {
            let known = if b.meets(elem, Bound::Dup) {
                "Copy or Shared (`Dup`), and not known to be Copy without a `Copy` bound"
            } else {
                "declared `?Dup`, so it may be Affine"
            };
            return d.with_rule(format!("the type parameter `{shown}` is {known} (§4.5)")).with_rule(IN_PLACE);
        }
        let kind = [(Bound::Copy, Kind::Copy), (Bound::Dup, Kind::Shared)].into_iter().find(|&(x, _)| b.meets(elem, x));
        let kind = kind.map_or(Kind::Affine, |(_, k)| k);
        d.with_rule(format!("`{shown}` is {} (§4.6)", kind.name())).with_rule(IN_PLACE)
    }
}
