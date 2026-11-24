import MassFitSpec
import AcceptanceSpec

/- The only intentional holes in the review: the frozen challenge, excluded
from the solution imports. Comparator must reject holes in any solution. -/
namespace YMReview.QCD
theorem mass_fit_correct : MassFitCorrect := by sorry
theorem six_pair_difference : SixPairDifference := by sorry
theorem acceptance : Acceptance := by sorry
end YMReview.QCD
