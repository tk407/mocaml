unset title
set key bottom right
set xlabel 'List size'
set ylabel 'Time (s)'
set logscale y
set nolog x
#set nolog xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set output "sorter_exec_times.eps" 
set size 1.,1.

plot "sorter_cont_data_clean_realtime.txt" using 1:2 with lp title 'cont', \
"sorter_mcon_data_clean_realtime.txt" using 1:2 with lp title 'mcon', \
"sorter_promise_data_clean_realtime.txt" using 1:2 with lp title 'promise', \
"sorter_sys_data_clean_realtime.txt" using 1:2 with lp title 'sys', \
"sorter_tramp_data_clean_realtime.txt" using 1:2 with lp title 'tramp', \
"sorter_vm_data_clean_realtime.txt" using 1:2 with lp title 'vm', \
"sorter_lwt_data_clean_realtime.txt" using 1:2 with lp title 'lwt'


unset title 
set xlabel 'List size'
set ylabel 'Time (s)'
set logscale y
set nolog x
#set nolog xy
set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set output "sorter_exec_times_bw.eps" 
replot

unset title
set key top left
set xlabel 'List size'
set ylabel 'Memory (word)'
set nolog xy
#set logscale y
#set nolog xy
set term post eps enhanced color fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set size 1.,1.
set output "sorter_mem.eps" 

plot "sorter_cont_data_clean_mem.txt" using 1:2 with lp title 'cont', \
"sorter_mcon_data_clean_mem.txt" using 1:2 with lp title 'mcon', \
"sorter_promise_data_clean_mem.txt" using 1:2 with lp title 'promise', \
"sorter_sys_data_clean_mem.txt" using 1:2 with lp title 'sys', \
"sorter_tramp_data_clean_mem.txt" using 1:2 with lp title 'tramp', \
"sorter_vm_data_clean_mem.txt" using 1:2 with lp title 'vm', \
"sorter_lwt_data_clean_mem.txt" using 1:2 with lp title 'lwt'


set term post eps enhanced mono fontfile "/usr/share/texmf/fonts/type1/public/cm-super/sfss1200.pfb" "SFSS1200"
set output "sorter_mem_bw.eps" 
replot


