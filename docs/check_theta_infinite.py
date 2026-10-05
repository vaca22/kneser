"""Small independent algebra checks; execute on galic."""
from fractions import Fraction as Q
import json
import unittest
from theta_infinite import reduce_bounds, upward_dyadic


class BlockBoundsTests(unittest.TestCase):
    def test_outward_coarsening(self):
        for value in [Q(0), Q(1,3), Q(1,2**800), Q(2**600,3)]:
            rounded=upward_dyadic(value)
            self.assertLessEqual(value,rounded)
            self.assertLess(rounded-value,Q(1,2**40))

    def test_high_precision_tail_serializes(self):
        rho=upward_dyadic(Q(51,100)+Q(1,2**500))
        got=reduce_bounds(150,Q(11,20),Q(1,10**30),Q(1,20),
                          Q(1,10**51),rho,Q(1000),Q(10))
        self.assertTrue(got['passed'])
        # Regression: uncoarsened dyadic powers exceed Python's default
        # integer string limit during certificate serialization.
        encoded=json.dumps({k:str(v) for k,v in got.items()})
        self.assertGreater(len(encoded),0)

    def test_exact_example(self):
        # n=2, r=1/2, rho=1/4, K=1: C_low=C_tail=1/2.
        got=reduce_bounds(2,Q(1,2),Q(1),Q(1,4),Q(1,100),Q(1,4),Q(1),Q(1,10))
        self.assertEqual([got[k] for k in ['a','b','c','d']],
                         [Q(1,4),Q(1,8),Q(1,4),Q(1,8)])
        self.assertEqual(got['q'],Q(1,2))
        self.assertEqual(got['defect'],Q(3,50))
        self.assertEqual(got['distance'],Q(3,25))
        self.assertTrue(got['passed'])

    def test_finite_pass_can_fail_infinite(self):
        got=reduce_bounds(2,Q(1,2),Q(1,100),Q(1,4),Q(0),Q(1,4),Q(1),Q(1))
        self.assertLess(got['q'],1)
        self.assertFalse(got['passed'])  # the output tail does not fit the ball

    def test_noncontractive_block(self):
        got=reduce_bounds(2,Q(1,2),Q(1),Q(1,4),Q(0),Q(1,4),Q(100),Q(0))
        self.assertGreater(got['q'],1)
        self.assertIsNone(got['distance'])
        self.assertFalse(got['passed'])

    def test_unbounded_input_evaluation_rejected(self):
        for rho in [Q(1,2),Q(3,4)]:
            with self.assertRaises(AssertionError):
                reduce_bounds(2,Q(1,2),Q(1),Q(0),Q(0),rho,Q(1),Q(1))


if __name__=='__main__': unittest.main()
