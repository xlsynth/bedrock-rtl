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
from ecc.scripts.hsiao_secded import hsiao_secded_code, get_r, get_n, get_H, get_G


class TestHsiaoSecdedCode(unittest.TestCase):

    @parameterized.expand(
        [
            (4, 4),
            (8, 5),
            (16, 6),
            (32, 7),
            (64, 8),
            (128, 9),
            (256, 10),
            (512, 11),
            (1024, 12),
        ]
    )
    def test_get_r_pow_of_2(self, k, expected_r):
        self.assertEqual(get_r(k), expected_r)

    @parameterized.expand(
        [
            (3, 4),
            (7, 5),
            (15, 6),
            (31, 7),
            (60, 8),
        ]
    )
    def test_get_r_non_pow_of_2(self, k, expected_r):
        self.assertEqual(get_r(k), expected_r)

    @parameterized.expand(
        [
            (4, 3, 7),
            (8, 4, 12),
            (16, 5, 21),
        ]
    )
    def test_get_n(self, k, r, expected_n):
        self.assertEqual(get_n(k, r), expected_n)

    @parameterized.expand(
        [
            (4, 4, 8),
            (8, 5, 13),
            (16, 6, 22),
            (32, 7, 39),
            (64, 8, 72),
        ]
    )
    def test_hsiao_secded_code(self, k, expected_r, expected_n):
        r, n, H, G = hsiao_secded_code(k)

        # Check the number of parity and codeword bits
        self.assertEqual(r, expected_r)
        self.assertEqual(n, expected_n)

        # Check the dimensions of the matrices
        self.assertEqual(H.shape, (r, n))
        self.assertEqual(G.shape, (k, n))

        # Check if the parity-check matrix H has the correct properties
        for column in H.T:
            self.assertEqual(
                sum(column) % 2, 1
            )  # Each column should have an odd number of 1s

        # Check if the generator matrix G is correctly formed
        I_k = np.identity(k, dtype=int)
        self.assertTrue(
            np.array_equal(G[:, :k], I_k)
        )  # First k columns should be identity matrix

    def test_invalid_k(self):
        with self.assertRaises(ValueError):
            hsiao_secded_code(0)  # Invalid k, should raise an error


if __name__ == "__main__":
    unittest.main()
