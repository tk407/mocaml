set title 'title'
set xlabel 'xlabel'
set ylabel 'ylabel'
set logscale y
set terminal postscript portrait enhanced mono dashed lw 1 "Helvetica" 14
set output "sorter_exec_times.ps" 

plot "sorter_cont_data_clean.txt" using 1:2 with lp title 'cont', \
"sorter_mcon_data_clean.txt" using 1:2 with lp title 'mcon', \
"sorter_promise_data_clean.txt" using 1:2 with lp title 'promise', \
"sorter_sys_data_clean.txt" using 1:2 with lp title 'sys', \
"sorter_tramp_data_clean.txt" using 1:2 with lp title 'tramp', \
"sorter_vm_data_clean.txt" using 1:2 with lp title 'vm', \
"sorter_lwt_data_clean.txt" using 1:2 with lp title 'lwt'


