# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2022.09
# platform  : Linux 4.18.0-553.47.1.el8_10.x86_64
# version   : 2022.09p002 64 bits
# build date: 2022.11.24 12:29:17 UTC
# ----------------------------------------
# started   : 2025-09-16 08:43:28 IST
# hostname  : Cadence_SERVER.(none)
# pid       : 824857
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:34169' '-style' 'windows' '-data' 'AAAAyHicY2RgYLCp////PwMYMFcBCQEGHwZfhiAGVyDpzxAGpBkYvBhMGYwYLBgMGBwYDBksgWw9IG0GFNFjMAfzTBlMGKyIUgUGjA8gNIMNIwMyYAxsQKEZGFhhCkGiYOelMSQyZDLkAI0rYUgG0kAAAGqbFJ8=' '-proj' '/home/src2024/formal/i2c/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/src2024/formal/i2c/jgproject/.tmp/.initCmds.tcl' 'fail.tcl'
clear -all

set MAIN_PATH [pwd]

# Analyze Verilog files from filelist
analyze -v2k -f ${MAIN_PATH}/i2c.f

# Analyze SystemVerilog top module
analyze -sv12 ${MAIN_PATH}/rtl/i2c_master_top.sv
analyze -sv12 ${MAIN_PATH}/fail/assert.sv

# Initialize coverage
# check_cov -init -model all

# Elaborate the design
elaborate -top i2c_master_top

# Set clock and reset
clock wb_clk_i
#reset wb_rst_i 
reset -expr {wb_rst_i ~arst_i}

# Run formal verification
prove -all

# Measure coverage
#  check_cov -measure -time_limit 2h
#  check_cov -report -no_return -report_file report.txt -force -exclude { reset waived } -checker COI
#  check_cov -report -no_return -report_file cover.html \
#      -html -force -exclude { reset waived } -checker COI

# Generate report
# report -summary -force -result -file i2c.fpv.rpt

# Exit JasperGold
# exit -force

include fail.tcl
