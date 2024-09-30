
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 0 * x + 2 * y + 0 * x * y) % 4' (0, 37, 41, 306, 307, 308, 309, 310, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261, 3262, 3263, 3264, 3265, 3266, 3304, 3305, 3306, 3307, 3308, 3309, 3310, 3311, 3312, 3313, 3314, 3315, 3316, 3317, 3318, 3319, 3320, 3321, 3322, 3323, 3324, 3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334, 3335, 3336, 3337, 3338, 3339, 3340, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540, 3541, 3542, 3543, 4267, 4268, 4269, 4270, 4281, 4282, 4283, 4284, 4285, 4286, 4287, 4288, 4313, 4314, 4315, 4316, 4317, 4318, 4338, 4339, 4340, 4341, 4356, 4357, 4358, 4359, 4360, 4582, 4583, 4584, 4585, 4586, 4587, 4588, 4589, 4590, 4591, 4592, 4593, 4594, 4595, 4596, 4597, 4598, 4599, 4600, 4601, 4602, 4603, 4604, 4605, 4606, 4607, 4608, 4609, 4610, 4611, 4612, 4613, 4614, 4615, 4616, 4617, 4618, 4619, 4620, 4621, 4622, 4623, 4624, 4625, 4626, 4627, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636, 4637, 4638, 4639, 4640, 4641, 4642, 4643, 4644, 4645, 4646, 4647, 4648, 4649, 4650, 4651, 4652, 4653, 4654, 4655, 4656, 4657, 4658, 4659, 4660, 4661, 4662, 4663, 4664, 4665, 4666, 4667, 4668, 4669, 4670, 4671, 4672, 4673, 4674, 4675, 4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686, 4687, 4688, 4689, 4690, 4691, 4692, 4693)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² + 2 * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y + 2 * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + 2 * y² + 2 * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [325, 326, 3544, 4359, 4360, 4683, 4688, 4689] [2, 3, 8, 23, 39, 40, 43, 47, 99, 151, 203, 255, 312, 313, 315, 316, 332, 333, 335, 336, 359, 407, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3268, 3269, 3271, 3272, 3278, 3279, 3281, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3471, 3472, 3474, 3475, 3481, 3482, 3484, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3862, 4055, 4065, 4258, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4368, 4373, 4380, 4539, 4547, 4571] :=
    ⟨Fin 4, «FinitePoly 2 * x² + 2 * y² + 2 * y % 4», by decideFin!⟩