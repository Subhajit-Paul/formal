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

# SP

#assume -env {wb_dat_i[2:1] == 2'b00} -name reserved_bit_zero_for_data_input
#assume -env {cr[2:1] == 2'b00} -name reserved_bit_zero_for_command_register
#assume -env {sr[4:2] == 2'b00} -name reserved_bit_zero_for_status_register
#assume -env {!(wb_dat_i[4] && wb_dat_i[5])} -name read_write_not_zero_at_same_time
#assume -env {!(wb_dat_i[7] && wb_dat_i[6])} -name start_stop_not_zero_at_same_time
#assume -env {ctr[5:0] == 6'h0} -name reserved_bit_zero_for_status_control_register


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

