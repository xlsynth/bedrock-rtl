# SPDX-License-Identifier: Apache-2.0

# Enable every warning and treat every enabled warning as an error.
-Weverything
-Werror

# Public packages intentionally expose APIs unused by individual designs.
-Wno-unused-package-subroutine
-Wno-unused-package-parameter
-Wno-unused-package-typedef

# Transitive source sets contain reusable modules unrelated to the selected top.
-Wno-unused-def

# Parameter-dependent width casts are necessary even when one instance makes them identity casts.
-Wno-useless-cast

# Explicit default branches intentionally keep unique case statements defensive.
-Wno-case-redundant-default

# Signed integer dimension parameters are deliberately compared with unsigned bounded signals.
-Wno-sign-compare

# Parameterized arithmetic intentionally combines differently sized operands; width checks remain on.
-Wno-arith-op-mismatch

# Equal-width packed-array reshaping is fundamental to tiled and multidimensional RTL interfaces.
-Wno-packed-array-conv
-Wno-comparison-mismatch
-Wno-bitwise-op-mismatch

# Explicitly empty output connections already document an intentional unused output.
-Wno-empty-output-connection
