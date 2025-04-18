# Copyright 2024-2025 The Bedrock-RTL Authors
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
from concurrent.futures import ProcessPoolExecutor
from python.eccgen.hsiao_secded import (
    hsiao_secded_code,
    get_r,
    check_construction,
    encode,
    decode_syndrome,
    decode_message,
)

# Cache code constructions to speed up tests on the same construction.
# Key is message length (k)
# RTL supported codes
CODES = {
    4: hsiao_secded_code(4),
    8: hsiao_secded_code(8),
    11: hsiao_secded_code(11),
    16: hsiao_secded_code(16),
    26: hsiao_secded_code(26),
    32: hsiao_secded_code(32),
    57: hsiao_secded_code(57),
    64: hsiao_secded_code(64),
    120: hsiao_secded_code(120),
    128: hsiao_secded_code(128),
    247: hsiao_secded_code(247),
    256: hsiao_secded_code(256),
}


def _check_single_error_exhaustive(m, k, n, H, G):
    c = encode(m, G)
    for loc in range(n):
        rc = c.copy()
        rc[loc] = 1 - c[loc]
        s = decode_syndrome(rc, H, k)
        assert (np.sum(s) % 2) == 1
        m_decoded, ce, due = decode_message(rc, s, H)
        assert np.array_equal(m, m_decoded)
        assert ce
        assert not due


def _check_double_error_exhaustive(m, k, n, H, G):
    c = encode(m, G)
    for loc0 in range(n):
        for loc1 in range(n):
            if loc0 == loc1:
                continue
            rc = c.copy()
            rc[loc0] = 1 - rc[loc0]
            rc[loc1] = 1 - rc[loc1]
            s = decode_syndrome(rc, H, k)
            assert (np.sum(s) % 2) == 0
            _, ce, due = decode_message(rc, s, H)
            assert not ce
            assert due


def _check_triple_error_random(m, k, n, H, G):
    for _ in range(100):
        c = encode(m, G)
        # Infeasible to do this exhaustively for large n
        locs = np.random.choice(n, 3, replace=False)
        rc = c.copy()
        for loc in locs:
            rc[loc] = 1 - rc[loc]
        s = decode_syndrome(rc, H, k)
        assert (np.sum(s) % 2) == 1
        _, ce, due = decode_message(rc, s, H)
        # Triple bit error must not go undetected
        assert ce ^ due


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

    def test_hsiao_secded_k4(self):
        _, _, H, G = CODES[4]
        check_construction(G, H)
        H_expected = np.array(
            [
                [0, 1, 1, 1, 1, 0, 0, 0],
                [1, 0, 1, 1, 0, 1, 0, 0],
                [1, 1, 0, 1, 0, 0, 1, 0],
                [1, 1, 1, 0, 0, 0, 0, 1],
            ]
        )
        G_expected = np.array(
            [
                [1, 0, 0, 0, 0, 1, 1, 1],
                [0, 1, 0, 0, 1, 0, 1, 1],
                [0, 0, 1, 0, 1, 1, 0, 1],
                [0, 0, 0, 1, 1, 1, 1, 0],
            ]
        )
        self.assertTrue(np.array_equal(H, H_expected))
        self.assertTrue(np.array_equal(G, G_expected))

    @parameterized.expand(CODES.keys())
    def test_hsiao_secded_code_construction(self, k):
        _, _, H, G = CODES[k]
        check_construction(G, H)

    def test_invalid_k(self):
        with self.assertRaises(ValueError):
            hsiao_secded_code(0)

    @parameterized.expand([4, 8, 15, 16])
    def test_encode_decode_syndrome_exhaustive(self, k):
        """Test message encoding and syndrome decoding exhaustively for smaller codes without any errors."""
        r, n, H, G = CODES[k]
        for m in range(2**k):
            m = np.array([int(b) for b in format(m, f"0{k}b")])
            c = encode(m, G)
            self.assertEqual(c.shape, (n,))
            # Decode the codeword and check that syndrome is zero
            s = decode_syndrome(c, H, k)
            self.assertTrue(np.array_equal(s, np.zeros(r, dtype=int)))

    @parameterized.expand(CODES.keys())
    def test_encode_decode_syndrome_random(self, k):
        """Test a bunch of random messages. Note that doing it exhaustively is infeasible for large k."""
        r, n, H, G = CODES[k]
        np.random.seed(42)
        for _ in range(1000):
            m = np.random.randint(0, 2, k)
            c = encode(m, G)
            self.assertEqual(c.shape, (n,))
            # Decode the codeword and check that syndrome is zero
            s = decode_syndrome(c, H, k)
            self.assertTrue(np.array_equal(s, np.zeros(r, dtype=int)))

    @parameterized.expand(CODES.keys())
    def test_encode_decode_single_error_injection(self, k):
        _, n, H, G = CODES[k]
        np.random.seed(42)
        # The code's characteristics are independent of the message (it's a linear code!).
        # But test on 10 random messages just to be sure.
        messages = [np.random.randint(0, 2, k) for _ in range(10)]
        with ProcessPoolExecutor() as executor:
            executor.map(
                lambda m: _check_single_error_exhaustive(m, k, n, H, G), messages
            )

    @parameterized.expand(CODES.keys())
    def test_encode_decode_double_error_injection(self, k):
        _, n, H, G = CODES[k]
        np.random.seed(42)
        # The code's characteristics are independent of the message (it's a linear code!).
        # But test on 10 random messages just to be sure.
        messages = [np.random.randint(0, 2, k) for _ in range(10)]
        with ProcessPoolExecutor() as executor:
            executor.map(
                lambda m: _check_double_error_exhaustive(m, k, n, H, G), messages
            )

    @parameterized.expand(CODES.keys())
    def test_encode_decode_triple_error_injection(self, k):
        _, n, H, G = CODES[k]
        np.random.seed(42)
        # The code's characteristics are independent of the message (it's a linear code!).
        # But test on 10 random messages just to be sure.
        messages = [np.random.randint(0, 2, k) for _ in range(10)]
        with ProcessPoolExecutor() as executor:
            executor.map(lambda m: _check_triple_error_random(m, k, n, H, G), messages)


if __name__ == "__main__":
    unittest.main()
