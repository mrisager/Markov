import T1MertensVKFromRegion
import RiemannGaussian.ZetaVinogradovZeroFree

/-! Both branches of the original Theorem 1, with the same genuine
Euclidean-area coefficient and the actual sorted positive triple count. -/

namespace Markov

theorem t1_mertens_vk : t1_MertensVKBound :=
  t1_mertens_vk_of_region t1_VKZeroFreeRegion_proved

theorem t1_markovUnconditional : UnconditionalBound t1_markovLeadingCoefficient :=
  t1_markovUnconditional_of_vk_region t1_VKZeroFreeRegion_proved

theorem t1_mainTheorem : MainTheorem :=
  t1_mainTheorem_of_vk_region t1_VKZeroFreeRegion_proved

end Markov
