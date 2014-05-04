set title 'title'
set xlabel 'xlabel'
set ylabel 'ylabel'
set logscale xy
set terminal postscript portrait enhanced mono dashed lw 1 "Helvetica" 14
set output "kpn_exec_times.ps" 

plot "kpn_cont_data_clean.txt" using 1:2 with lp title 'cont', \
"kpn_mcon_data_clean.txt" using 1:2 with lp title 'mcon', \
"kpn_promise_data_clean.txt" using 1:2 with lp title 'promise', \
"kpn_sys_data_clean.txt" using 1:2 with lp title 'sys', \
"kpn_tramp_data_clean.txt" using 1:2 with lp title 'tramp', \
"kpn_vm_data_clean.txt" using 1:2 with lp title 'vm'


