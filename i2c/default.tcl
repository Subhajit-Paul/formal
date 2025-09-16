clear -all

set MAIN_PATH [pwd]

# Analyze Verilog files from filelist
analyze -v2k -f ${MAIN_PATH}/i2c.f

# Analyze SystemVerilog top module
analyze -sv12 ${MAIN_PATH}/rtl/i2c_master_top.sv
analyze -sv12 ${MAIN_PATH}/default/assert.sv

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

