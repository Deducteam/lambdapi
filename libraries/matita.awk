BEGIN{r=0}
/def le_fact_1z :/{r=1;print"le_fact_1z :";next}
/:=/{if(r==1){print".\n(; :=";r=0;next}else{print;next}}
/def ab_times_cd :/{print";)\n",$0;next}
{print;next}
