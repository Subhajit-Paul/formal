# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2022.09
# platform  : Linux 4.18.0-553.47.1.el8_10.x86_64
# version   : 2022.09p002 64 bits
# build date: 2022.11.24 12:29:17 UTC
# ----------------------------------------
# started   : 2025-09-16 07:35:20 IST
# hostname  : Cadence_SERVER.(none)
# pid       : 821614
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:40357' '-style' 'windows' '-data' 'AAAAznicY2RgYLCp////PwMYMFcBCQEGHwZfhiAGVyDpzxAGpBkYvBhMGYwYLBgMGBwYDBksgWw9IG0GFNFjMAfzTBlMGKyIUgUGjA8gNIMNIwMyYAxsQKEZGFhhCkGiQCzGkMKQypDGkMhQypDDUAI0tIQhGcgCAgDxaBXu' '-proj' '/home/src2024/formal/i2c/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/src2024/formal/i2c/jgproject/.tmp/.initCmds.tcl' 'default.tcl'
clear -all

set MAIN_PATH [pwd]

# Analyze Verilog files from filelist
analyze -v2k -f ${MAIN_PATH}/i2c.f

# Analyze SystemVerilog top module
analyze -sv12 ${MAIN_PATH}/rtl/i2c_master_top.sv
analyze -sv12 ${MAIN_PATH}/default/assert.sv
include default.tcl
include default.tcl
include default.tcl
include default.tcl
include default.tcl
include default.tcl
include default.tcl
include default.tcl
include default.tcl
include default.tcl
