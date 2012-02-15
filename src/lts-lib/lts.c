// -*- tab-width:4 ; indent-tabs-mode:nil -*-
#include <config.h>

#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#include <hre/user.h>
#include <lts-io/provider.h>
#include <lts-lib/lts.h>
#include <tables.h>

lts_t lts_create(){
    lts_t lts=(lts_t)RTmallocZero(sizeof(struct lts));
    lts->type=LTS_LIST;
    lts->tau=-1;
    return lts;
}

void lts_free(lts_t lts){
    free(lts->begin);
    free(lts->src);
    free(lts->label);
    free(lts->dest);
    free(lts);
}

static void build_block(uint32_t states,uint32_t transitions,u_int32_t *begin,u_int32_t *block,u_int32_t *label,u_int32_t *other){
    uint32_t i;
    uint32_t loc1,loc2;
    u_int32_t tmp_label1,tmp_label2;
    u_int32_t tmp_other1,tmp_other2;

    for(i=0;i<states;i++) begin[i]=0;
    for(i=0;i<transitions;i++) begin[block[i]]++;
    for(i=1;i<states;i++) begin[i]=begin[i]+begin[i-1];
    for(i=transitions;i>0;){
        i--;
        block[i]=--begin[block[i]];
    }
    begin[states]=transitions;
    for(i=0;i<transitions;i++){
        if (block[i]==i) {
            continue;
        }
        loc1=block[i];
        tmp_label1=label[i];
        tmp_other1=other[i];
        for(;;){
            if (loc1==i) {
                block[i]=i;
                label[i]=tmp_label1;
                other[i]=tmp_other1;
                break;
            }
            loc2=block[loc1];
            tmp_label2=label[loc1];
            tmp_other2=other[loc1];
            block[loc1]=loc1;
            label[loc1]=tmp_label1;
            other[loc1]=tmp_other1;
            if (loc2==i) {
                block[i]=i;
                label[i]=tmp_label2;
                other[i]=tmp_other2;
                break;
            }
            loc1=block[loc2];
            tmp_label1=label[loc2];
            tmp_other1=other[loc2];
            block[loc2]=loc2;
            label[loc2]=tmp_label2;
            other[loc2]=tmp_other2;
        }
    }
}

void lts_set_type(lts_t lts,LTS_TYPE type){
    uint32_t i,j;

    if (lts->type==type) return; /* no type change */

    /* first change to LTS_LIST */
    switch(lts->type){
        case LTS_LIST:
            lts->begin=(u_int32_t*)RTmalloc(sizeof(u_int32_t)*(lts->states+1));
            break;
        case LTS_BLOCK:
            lts->src=(u_int32_t*)RTmalloc(sizeof(u_int32_t)*(lts->transitions));
            for(i=0;i<lts->states;i++){
                for(j=lts->begin[i];j<lts->begin[i+1];j++){
                    lts->src[j]=i;
                }
            }
            break;
        case LTS_BLOCK_INV:
            lts->dest=(u_int32_t*)RTmalloc(sizeof(u_int32_t)*(lts->transitions));
            for(i=0;i<lts->states;i++){
                for(j=lts->begin[i];j<lts->begin[i+1];j++){
                    lts->dest[j]=i;
                }
            }
            break;
    }
// MEMSTAT_CHECK;
    /* then change to required type */
    lts->type=type;
    switch(type){
        case LTS_LIST:
            free(lts->begin);
            lts->begin=NULL;
            return;
        case LTS_BLOCK:
            build_block(lts->states,lts->transitions,lts->begin,lts->src,lts->label,lts->dest);
            free(lts->src);
            lts->src=NULL;
            return;
        case LTS_BLOCK_INV:
            build_block(lts->states,lts->transitions,lts->begin,lts->dest,lts->label,lts->src);
            free(lts->dest);
            lts->dest=NULL;
            return;
    }
}

static void lts_realloc(lts_t lts){
    int N,K;
    if (lts->ltstype){
        N=lts_type_get_state_label_count(lts->ltstype);
        K=lts_type_get_edge_label_count(lts->ltstype);
    } else {
        N=0;
        K=1;
    }
    uint32_t size;
    // realloc root_list
    size=sizeof(u_int32_t)*lts->root_count;
    lts->root_list=(uint32_t*)RTrealloc(lts->root_list,size);
    if (size && lts->root_list==NULL) Abort("out of memory");
    // realloc properties
    if (N>0) {
        size=sizeof(u_int32_t)*lts->states;
        lts->properties=(uint32_t*)RTrealloc(lts->properties,size);
        if (size && lts->properties==NULL) Abort("out of memory");
    } else {
        lts->properties=NULL;
    }
    switch(lts->type){
        case LTS_BLOCK:
            break;
        case LTS_BLOCK_INV:
            break;
        case LTS_LIST:
            break;
        default:
            Abort("undefined ");
    }
    // realloc begin
    switch(lts->type){
        case LTS_BLOCK:
        case LTS_BLOCK_INV:
            size=sizeof(u_int32_t)*(lts->states+1);
            break;
        case LTS_LIST:
            size=0;
            break;
    }
    lts->begin=(u_int32_t*)RTrealloc(lts->begin,size);
    if (size && lts->begin==NULL) Abort("out of memory");
    // realloc src
    switch(lts->type){
        case LTS_BLOCK:
            size=0;
            break;
        case LTS_BLOCK_INV:
        case LTS_LIST:
            size=sizeof(u_int32_t)*(lts->transitions);
            break;
    }
    lts->src=(u_int32_t*)RTrealloc(lts->src,size);
    if (size && lts->src==NULL) Abort("out of memory");
    // realloc dest
    switch(lts->type){
        case LTS_BLOCK_INV:
            size=0;
            break;
        case LTS_BLOCK:
        case LTS_LIST:
            size=sizeof(u_int32_t)*(lts->transitions);
            break;
    }
    lts->dest=(u_int32_t*)RTrealloc(lts->dest,size);
    if (size && lts->dest==NULL) Abort("out of memory");
    // realloc label
    size=(K>0)?(sizeof(u_int32_t)*(lts->transitions)):0;
    lts->label=(u_int32_t*)RTrealloc(lts->label,size);
    if (size && lts->label==NULL) Abort("out of memory");
}

void lts_set_sig_given(lts_t lts,lts_type_t type,value_table_t *values){
    if (lts->ltstype) Abort("type change unimplemented");
    lts->ltstype=type;
    int V=lts_type_get_state_length(type);
    if (V>0) {
        lts->state_db=TreeDBScreate(V);
    }
    int N=lts_type_get_state_label_count(type);
    if (N>1) {
        lts->prop_idx=TreeDBScreate(N);
    }
    int K=lts_type_get_edge_label_count(type);
    if (K>1) {
        lts->edge_idx=TreeDBScreate(K);
    }
    int T=lts_type_get_type_count(type);
    lts->values=(value_table_t*)RTmalloc(T*sizeof(value_table_t));
    for(int i=0;i<T;i++){
        lts->values[i]=values[i];
    }
    Print(infoShort,"realloc");
    lts_realloc(lts);
}

void lts_set_sig(lts_t lts,lts_type_t type){
    int T=lts_type_get_type_count(type);
    value_table_t values[T];
    for(int i=0;i<T;i++){
        char *sort=lts_type_get_type(type,i);
        switch(lts_type_get_format(type,i)){
        case LTStypeDirect:
        case LTStypeRange:
            values[i]=NULL;
            break;
        case LTStypeChunk:
        case LTStypeEnum:
            values[i]=chunk_table_create(NULL,sort);
            break;
        }
    }
    lts_set_sig_given(lts,type,values);
}

void lts_set_size(lts_t lts,u_int32_t roots,u_int32_t states,u_int32_t transitions){
    lts->root_count=roots;
    lts->states=states;
    lts->transitions=transitions;
    lts_realloc(lts);
}

void lts_sort(lts_t lts){
    uint32_t i,j,k,l,d;
    lts_set_type(lts,LTS_BLOCK);
    for(i=0;i<lts->states;i++){
        for(j=lts->begin[i];j<lts->begin[i+1];j++){
            l=lts->label[j];
            d=lts->dest[j];
            for(k=j;k>lts->begin[i];k--){
                if (lts->label[k-1]<l) break;
                if ((lts->label[k-1]==l)&&(lts->dest[k-1]<=d)) break;
                lts->label[k]=lts->label[k-1];
                lts->dest[k]=lts->dest[k-1];
            }
            lts->label[k]=l;
            lts->dest[k]=d;
        }
    }
}

void lts_sort_dest(lts_t lts){
    uint32_t i,j,k,l,d;
    lts_set_type(lts,LTS_BLOCK);
    for(i=0;i<lts->states;i++){
        for(j=lts->begin[i];j<lts->begin[i+1];j++){
            l=lts->label[j];
            d=lts->dest[j];
            for(k=j;k>lts->begin[i];k--){
                if (lts->dest[k-1]<d) break;
                if ((lts->dest[k-1]==d)&&(lts->label[k-1]<=l)) break;
                lts->label[k]=lts->label[k-1];
                lts->dest[k]=lts->dest[k-1];
            }
            lts->label[k]=l;
            lts->dest[k]=d;
        }
    }
}

static void pass1_dfs(lts_t lts,uint32_t tau,uint32_t *e_time,uint32_t *time,uint32_t state,uint32_t *count){
    if (e_time[state]>0) return;
    (*count)++;
    e_time[state]=1;
    for(uint32_t i=lts->begin[state];i<lts->begin[state+1];i++){
        if (lts->label[i]==tau) pass1_dfs(lts,tau,e_time,time,lts->dest[i],count);
    }
    (*time)++;
    e_time[state]=(*time);
}

static void pass2_dfs(lts_t lts,uint32_t tau,uint32_t *map,uint32_t component,uint32_t state){
    if(map[state]>0) return;
    map[state]=component;
    for(uint32_t i=lts->begin[state];i<lts->begin[state+1];i++){
        if (lts->label[i]==tau) pass2_dfs(lts,tau,map,component,lts->dest[i]);
    }
}

void lts_tau_cycle_elim(lts_t lts){
    uint32_t i,time,tmp,component,count,s,l,d,max;
    uint32_t *map;

    uint32_t tau=(unsigned int)lts->tau;
    /* mark with exit times */
    lts_set_type(lts,LTS_BLOCK);
    map=(uint32_t*)RTmalloc(sizeof(uint32_t)*lts->states);
    for(i=0;i<lts->states;i++) {
        map[i]=0;
    }
    time=1;
    max=0;
    for(i=0;i<lts->states;i++){
        uint32_t pass1_dfs_count=0;
        pass1_dfs(lts,tau,map,&time,i,&pass1_dfs_count);
        if (pass1_dfs_count>max) max=pass1_dfs_count;
    }
    Print(infoLong,"worst tau component has size %d",max);
    /* renumber: highest exit time means lowest number */
    /* at the same time reverse direction of edges */
    lts_set_type(lts,LTS_LIST);
    for(i=0;i<lts->root_count;i++){
        lts->root_list[i]=time-map[lts->root_list[i]];
    }
    for(i=0;i<lts->transitions;i++){
        tmp=lts->src[i];
        lts->src[i]=time-map[lts->dest[i]];
        lts->dest[i]=time-map[tmp];
    }
    /* mark components */
    lts_set_type(lts,LTS_BLOCK);
    for(i=0;i<lts->states;i++){
        map[i]=0;
    }
    component=0;
    for(i=0;i<lts->states;i++){
        if(map[i]==0){
            component++;
            pass2_dfs(lts,tau,map,component,i);
        }
    }
    /* divide out equivalence classes reverse direction of edges again */
    lts_set_type(lts,LTS_LIST);
    for(i=0;i<lts->root_count;i++){
        lts->root_list[i]=map[lts->root_list[i]]-1;
    }
    count=0;
    for(i=0;i<lts->transitions;i++){
        d=map[lts->src[i]]-1;
        s=map[lts->dest[i]]-1;
        l=lts->label[i];
        if ((l==tau)&&(s==d)) {
            continue;
        }
        lts->src[count]=s;
        lts->label[count]=l;
        lts->dest[count]=d;
        count++;
        if ((l==tau)&&(s>d)){
            Abort("tau from high to low");
        }
    }
    lts_set_size(lts,lts->root_count,component,count);
    free(map);
    lts_uniq(lts);
}

void lts_merge(lts_t lts1,lts_t lts2){
    Print(info,"** warning ** omitting signature check");
    if (lts1->state_db) Abort("lts_merge cannot deal with state vectors");
    if (lts1->properties) Abort("lts_merge cannot deal with state labels");
    if (lts1->edge_idx) Abort("lts_merge cannot deal with multiple edge labels");
    uint32_t init_count=lts1->root_count;
    uint32_t state_count=lts1->states;
    uint32_t trans_count=lts1->transitions;
    lts_set_type(lts1,LTS_LIST);
    lts_set_type(lts2,LTS_LIST);
    lts_set_size(lts1,lts1->root_count+lts2->root_count,
        lts1->states+lts2->states,lts1->transitions+lts2->transitions);
    for(uint32_t i=0;i<lts2->root_count;i++){
        lts1->root_list[init_count]=state_count+lts2->root_list[i];
    }
    for(uint32_t i=0;i<lts2->transitions;i++){
        lts1->src[trans_count+i]=state_count+lts2->src[i];
        lts1->dest[trans_count+i]=state_count+lts2->dest[i];
    }
    if (lts1->label) {
        int T1=lts_type_get_edge_label_typeno(lts1->ltstype,0);
        int T2=lts_type_get_edge_label_typeno(lts2->ltstype,0);
        int N=VTgetCount(lts2->values[T2]);
        int map[N];
        for(int i=0;i<N;i++){
            chunk c=VTgetChunk(lts2->values[T2],i);
            map[i]=VTputChunk(lts1->values[T1],c);
        }
        for(uint32_t i=0;i<lts2->transitions;i++){
            lts1->label[trans_count+i]=map[lts2->label[i]];
        }
    }
    lts_free(lts2);
}

lts_t lts_encode_edge(lts_t lts){
    lts_t res=lts_create();
    lts_set_type(res,LTS_LIST);
    lts_set_sig(res,single_action_type());
    lts_set_type(lts,LTS_LIST);
    uint32_t temp=lts->transitions+lts->root_count;
    int V=lts_type_get_state_length(lts->ltstype);
    if (V) temp+=lts->states;
    int N=lts_type_get_state_label_count(lts->ltstype);
    if (N) temp+=lts->states;
    int K=lts_type_get_edge_label_count(lts->ltstype);
    lts_set_size(res,1,lts->states + 1,temp);
    res->root_list[0]=0;
    Print(infoShort,"init");
    int init=VTputChunk(res->values[0],chunk_str("init"));
    uint32_t edge=0;
    for(uint32_t i=0;i<lts->root_count;i++){
        res->src[edge]=0;
        res->dest[edge]=lts->root_list[i]+1;
        res->label[edge]=init;
        edge++;
    }
    if (V) {
        int typeno[V];
        data_format_t format[V];
        for(int i=0;i<V;i++){
            typeno[i]=lts_type_get_state_typeno(lts->ltstype,i);
            format[i]=lts_type_get_format(lts->ltstype,typeno[i]);
        }
        int vector[V];
        for(uint32_t i=0;i<lts->states;i++){
            char label[65536];
            char *current=label;
            current+=sprintf(current,"state");
            TreeUnfold(lts->state_db,i,vector);
            for(int j=0;j<V;j++){
                switch(format[j]){
                case LTStypeDirect:
                case LTStypeRange:
                    current+=sprintf(current,"|%d",vector[j]);
                    break;
                case LTStypeChunk:
                case LTStypeEnum:
                    {
                    chunk label_c=VTgetChunk(lts->values[typeno[j]],vector[j]);
                    char label_s[label_c.len*2+6];
                    chunk2string(label_c,sizeof label_s,label_s);
                    current+=sprintf(current,"|%s",label_s);
                    }
                }
            }
            res->src[edge]=i+1;
            res->dest[edge]=i+1;
            res->label[edge]=VTputChunk(res->values[0],chunk_str(label));;
            edge++;
        }
    }
    if (N) {
        int typeno[N];
        data_format_t format[N];
        for(int i=0;i<N;i++){
            typeno[i]=lts_type_get_state_label_typeno(lts->ltstype,i);
            format[i]=lts_type_get_format(lts->ltstype,typeno[i]);
        }
        int vector[N];
        for(uint32_t i=0;i<lts->states;i++){

            char label[65536];
            char *current=label;
            current+=sprintf(current,"prop");
            if (N==1) vector[0]=lts->properties[i];
            if (N>1) {
                TreeUnfold(lts->prop_idx,lts->properties[i],vector);
            }
            for(int j=0;j<N;j++){
                switch(format[j]){
                case LTStypeDirect:
                case LTStypeRange:
                    current+=sprintf(current,"|%d",vector[j]);
                    break;
                case LTStypeChunk:
                case LTStypeEnum:
                    {
                    chunk label_c=VTgetChunk(lts->values[typeno[j]],vector[j]);
                    char label_s[label_c.len*2+6];
                    chunk2string(label_c,sizeof label_s,label_s);
                    current+=sprintf(current,"|%s",label_s);
                    }
                }
            }
            res->src[edge]=i+1;
            res->dest[edge]=i+1;
            res->label[edge]=VTputChunk(res->values[0],chunk_str(label));;
            edge++;
        }
    }

    {
        int typeno[K];
        data_format_t format[N];
        for(int i=0;i<K;i++){
            typeno[i]=lts_type_get_edge_label_typeno(lts->ltstype,i);
            format[i]=lts_type_get_format(lts->ltstype,typeno[i]);
        }
        int vector[K];
        for(uint32_t i=0;i<lts->transitions;i++){
            char label[65536];
            char *current=label;
            current+=sprintf(current,"edge");
            if (K==1) vector[0]=lts->label[i];
            if (K>1) {
                TreeUnfold(lts->edge_idx,lts->label[i],vector);
            }
            for(int j=0;j<K;j++){
                switch(format[j]){
                case LTStypeDirect:
                case LTStypeRange:
                    current+=sprintf(current,"|%d",vector[j]);
                    break;
                case LTStypeChunk:
                case LTStypeEnum:
                    {
                    chunk label_c=VTgetChunk(lts->values[typeno[j]],vector[j]);
                    char label_s[label_c.len*2+6];
                    chunk2string(label_c,sizeof label_s,label_s);
                    current+=sprintf(current,"|%s",label_s);
                    }
                }
            }
            res->src[edge]=lts->src[i]+1;
            res->dest[edge]=lts->dest[i]+1;
            res->label[edge]=VTputChunk(res->values[0],chunk_str(label));;
            edge++;
        }
    }
    return res;
}

