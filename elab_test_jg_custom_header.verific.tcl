# SPDX-License-Identifier: Apache-2.0

# This file contains custom Tcl commands to run at the beginning of a Verific elaboration
# test on an FPV monitor intended for use with JasperGold.

# Demote VERI-1063 ("instantiating unknown module") from warning to info.
# This is because the jasper_scoreboard_3 module is encrypted from Cadence and
# Verific cannot see it.
#
# NOTE: This is really a hack -- we only want to exclude that specific module on specific tests.
# But unfortunately it means anyone using this demotion will have Verific
# spuriously pass elab tests if any modules are unknown. Use this file sparingly.
setmsgtype -info VERI-1063
