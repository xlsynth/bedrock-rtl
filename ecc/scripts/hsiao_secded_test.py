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
    check_columns_unique,
    check_column_weights_are_odd,
    encode,
    decode_syndrome,
    decode_message,
    parity_check_message_columns,
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

    def test_parity_check_message_columns(self):
        self.assertTrue(check_columns_unique(parity_check_message_columns(7, 32, 3)))
        self.assertTrue(
            check_column_weights_are_odd(parity_check_message_columns(7, 32, 3))
        )

    @parameterized.expand(
        [
            ("k4", 4, 4, 8),
            ("k8", 8, 5, 13),
            ("k15", 15, 6, 21),
            ("k16", 16, 6, 22),
            ("k30", 30, 7, 37),
            ("k32", 32, 7, 39),
            ("k59", 59, 8, 67),
            ("k64", 64, 8, 72),
            ("k128", 128, 9, 137),
        ]
    )
    def test_hsiao_secded_code_construction(self, name, k, expected_r, expected_n):
        r, n, H, G = hsiao_secded_code(k)

        # Check the number of parity and codeword bits
        self.assertEqual(r, expected_r)
        self.assertEqual(n, expected_n)

        # Check the dimensions of the matrices
        self.assertEqual(H.shape, (r, n))
        self.assertEqual(G.shape, (k, n))

        # Check that both matrices contain identity matrices in the right positions (suggesting systematic form)
        I_k = np.identity(k, dtype=int)
        I_r = np.identity(r, dtype=int)
        self.assertTrue(np.array_equal(G[:, :k], I_k))
        self.assertTrue(np.array_equal(H[:, k:], I_r))

        # Check that both matrices contain unique columns
        self.assertTrue(check_columns_unique(H))
        self.assertTrue(check_columns_unique(G))

        self.assertTrue(check_column_weights_are_odd(H))

    def test_invalid_k(self):
        with self.assertRaises(ValueError):
            hsiao_secded_code(0)

    @parameterized.expand(
        [
            ("k4", 4, 4, 8),
            ("k8", 8, 5, 13),
            ("k15", 15, 6, 21),
            ("k16", 16, 6, 22),
        ]
    )
    def test_encode_decode_syndrome_exhaustive(self, name, k, expected_r, expected_n):
        """Test message encoding and syndrome decoding exhaustively for smaller codes without any errors."""
        r, n, H, G = hsiao_secded_code(k)
        for m in range(2**k):
            m = np.array([int(b) for b in format(m, f"0{k}b")])
            c = encode(m, G)
            self.assertEqual(c.shape, (n,))
            # Decode the codeword and check that syndrome is zero
            s = decode_syndrome(c, H, k)
            self.assertTrue(np.array_equal(s, np.zeros(r, dtype=int)))

    @parameterized.expand(
        [
            ("k30", 30, 7, 37),
            ("k32", 32, 7, 39),
            ("k59", 59, 8, 67),
            ("k64", 64, 8, 72),
            ("k128", 128, 9, 137),
            ("k977", 977, 10, 987),
            ("k1024", 1024, 12, 1036),
        ]
    )
    def test_encode_decode_syndrome_random(self, name, k, expected_r, expected_n):
        """Test a bunch of random messages. Note that doing it exhaustively is infeasible for large k."""
        r, n, H, G = hsiao_secded_code(k)
        np.random.seed(42)
        for _ in range(1000):
            m = np.random.randint(0, 2, k)
            c = encode(m, G)
            self.assertEqual(c.shape, (n,))
            # Decode the codeword and check that syndrome is zero
            s = decode_syndrome(c, H, k)
            self.assertTrue(np.array_equal(s, np.zeros(r, dtype=int)))

    @parameterized.expand(
        [
            ("k4", 4),
            ("k8", 8),
            ("k15", 15),
            ("k16", 16),
            ("k30", 30),
            ("k32", 32),
            ("k59", 59),
            ("k64", 64),
            ("k128", 128),
            ("k977", 977),
            ("k1024", 1024),
        ]
    )
    def test_encode_decode_random_single_error_injection(self, name, k):
        r, n, H, G = hsiao_secded_code(k)
        np.random.seed(42)
        for _ in range(1000):
            m = np.random.randint(0, 2, k)
            c = encode(m, G)
            # Inject a single bit flip
            loc = np.random.randint(0, n)
            rc = c.copy()
            rc[loc] = 1 - c[loc]
            # Decode the codeword and check that syndrome is odd
            s = decode_syndrome(rc, H, k)
            self.assertTrue((np.sum(s) % 2) == 1)
            # Run the error correction algorithm and check that it corrects the error
            m_prime, ce, due = decode_message(rc, s, H)
            self.assertTrue(np.array_equal(m, m_prime))
            self.assertTrue(ce)
            self.assertFalse(due)

    @parameterized.expand(
        [
            ("k4", 4),
            ("k8", 8),
            ("k15", 15),
            ("k16", 16),
            ("k30", 30),
            ("k32", 32),
            ("k59", 59),
            ("k64", 64),
            ("k128", 128),
            ("k977", 977),
            ("k1024", 1024),
        ]
    )
    def test_encode_decode_random_double_error_injection(self, name, k):
        r, n, H, G = hsiao_secded_code(k)
        np.random.seed(42)
        for _ in range(1000):
            m = np.random.randint(0, 2, k)
            c = encode(m, G)
            # Inject a double bit flip
            locs = np.random.choice(n, 2, replace=False)
            rc = c.copy()
            for loc in locs:
                rc[loc] = 1 - c[loc]
            # Decode the codeword and check that syndrome is even
            s = decode_syndrome(rc, H, k)
            self.assertTrue((np.sum(s) % 2) == 0)
            # Run the error correction algorithm and check that it detects but doesn't correct the error
            _, ce, due = decode_message(rc, s, H)
            self.assertFalse(ce)
            self.assertTrue(due)


if __name__ == "__main__":
    unittest.main()
