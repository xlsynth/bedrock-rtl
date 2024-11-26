# Copyright 2024 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import unittest
import numpy as np
from parameterized import parameterized
from ecc.scripts.hsiao_secded import (
    hsiao_secded_code,
    get_r,
    get_n,
    get_H,
    get_G,
    check_columns_unique,
    check_columns_have_same_weight,
    check_column_weights_are_odd,
)


class TestHsiaoSecdedCode(unittest.TestCase):

    @parameterized.expand(
        [
            ("k4", 4, 4),
            ("k8", 8, 5),
            ("k16", 16, 6),
            ("k32", 32, 7),
            ("k64", 64, 8),
            ("k128", 128, 9),
            ("k256", 256, 10),
            ("k512", 512, 11),
            ("k1024", 1024, 12),
        ]
    )
    def test_get_r_pow_of_2(self, name, k, expected_r):
        self.assertEqual(get_r(k), expected_r)

    @parameterized.expand(
        [
            ("k3", 3, 4),
            ("k7", 7, 5),
            ("k15", 15, 6),
            ("k31", 31, 7),
            ("k60", 60, 8),
        ]
    )
    def test_get_r_non_pow_of_2(self, name, k, expected_r):
        self.assertEqual(get_r(k), expected_r)

    @parameterized.expand(
        [
            ("k4", 4, 3, 7),
            ("k8", 8, 4, 12),
            ("k16", 16, 5, 21),
        ]
    )
    def test_get_n(self, name, k, r, expected_n):
        self.assertEqual(get_n(k, r), expected_n)

    @parameterized.expand(
        [
            ("k4", 4, 4, 8),
            ("k8", 8, 5, 13),
            ("k15", 15, 6, 21),
            ("k16", 16, 6, 22),
            ("k30", 30, 7, 37),
            ("k32", 32, 7, 39),
            ("k59", 59, 8, 68),
            ("k64", 64, 8, 72),
            ("k128", 128, 9, 137),
        ]
    )
    def test_hsiao_secded_code(self, name, k, expected_r, expected_n):
        r, n, H, G = hsiao_secded_code(k)

        # Check the number of parity and codeword bits
        self.assertEqual(r, expected_r)
        self.assertEqual(n, expected_n)

        # Check the dimensions of the matrices
        self.assertEqual(H.shape, (r, n))
        self.assertEqual(G.shape, (k, n))

        # Check that the matrices both contain identity matrices (suggesting systematic form)
        I_k = np.identity(k, dtype=int)
        I_r = np.identity(r, dtype=int)
        self.assertTrue(np.array_equal(G[:, :k], I_k))
        self.assertTrue(np.array_equal(H[:, k:], I_r))

        self.assertTrue(check_columns_unique(H))
        self.assertTrue(check_column_weights_are_odd(H))
        self.assertTrue(check_columns_have_same_weight(H[:, :k]))
        self.assertTrue(check_columns_have_same_weight(H[:, k:]))
        self.assertTrue(check_columns_unique(G))

    def test_invalid_k(self):
        with self.assertRaises(ValueError):
            hsiao_secded_code(0)  # Invalid k, should raise an error


if __name__ == "__main__":
    unittest.main()
