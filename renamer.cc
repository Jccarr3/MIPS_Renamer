#include <assert.h>
#include <inttypes.h>
#include "renamer.h"
#include <vector>
#include <stdio.h>
#include <iostream>

using namespace std;

//constructor class definition
    renamer::renamer(uint64_t n_log_regs, uint64_t n_phys_regs, uint64_t n_branches, uint64_t n_active){
    //initial checks
    assert(n_phys_regs > n_log_regs);
    assert((n_branches > 0) && (n_branches < 65));
    assert(n_active > 0);
    
    //allocate space for primary data structures
        //make space for AMT and initialize to first n_log_regs of the PRF
    AMT.resize(n_log_regs);
    for(uint32_t i = 0; i < n_log_regs; i++){
        AMT[i] = i;
    }
        //make space for RMT and set it to AMT
    RMT.resize(n_log_regs);
    RMT = AMT;

    

        //Initialize PRF values to 0, ready bits to 0
    PRF.resize(n_phys_regs,0);
    PRF_ready.resize(n_phys_regs,true);

        //Free list initalizations
    Free_List.free_regs.resize(n_phys_regs - n_log_regs);
            //first n_log_regs bits are not allocated to free list
    for(uint32_t i = 0; i < (n_phys_regs-n_log_regs); i++){
        Free_List.free_regs[i] = i + n_log_regs;
    }
        
        //Active List initializations
    Active_List.active_regs.resize(n_active);

    GBM = 0;

        //Branch Checkpoint initlizations
    Branch_Checkpoints.resize(n_branches);
    for(int i = 0; i < n_branches; i++){
        Branch_Checkpoints[i].RMT_shadow.resize(n_log_regs);
    }
}

//Function to stall rename stage if free list is empty
bool renamer::stall_reg(uint64_t bundle_dst){
    uint32_t occupancy;
    uint32_t size = Free_List.free_regs.size();

    //set occupancy
    if(Free_List.h_phase != Free_List.t_phase){
        occupancy = Free_List.head - Free_List.tail;
    }
    else    occupancy = size - (Free_List.tail - Free_List.head);

    //check if full after bundles are added
    if((occupancy + bundle_dst)  > size){
        return true;
    }

    return false;

    
}

//Function to stall rename if too many unresolved branches
bool renamer::stall_branch(uint64_t bundle_branch){
    uint64_t tmp_gbm = GBM;
    uint32_t count = 0;

    //the following for loop checks the first bit in tmp_gbm then shift it right by 1
    for(uint32_t i = 0; i < Branch_Checkpoints.size(); i++){   
        if((tmp_gbm & 1) == 0){       //if the first bit is 0, then increase the count of free branch checkpoints
            count++;
        }

        if(count >= bundle_branch)   return false;       //if number of free spots is greater than branches coming in then return false

        tmp_gbm = tmp_gbm >> 1;
    }

    //cerr << "branch stall" << endl;
    return true;
}

//Function to return branch mask of instruction
uint64_t renamer::get_branch_mask(){
    return GBM;
}

//function to rename source registers
uint64_t renamer::rename_rsrc(uint64_t log_reg){
    //Get register name from RMT and return
    return RMT[log_reg]; 
}

//Function to rename destination register
uint64_t renamer::rename_rdst(uint64_t log_reg){
    //make sure there is a free physical register to use
    assert(!stall_reg(1));


    //set PRF_ready to false for the register being taken out of free list
    PRF_ready[Free_List.free_regs[Free_List.head]] = false;

    //get register name from Free List and set in RMT
    RMT[log_reg] = Free_List.free_regs[Free_List.head];
    
    //ensure wraparound is covered
    Free_List.head = (Free_List.head + 1) % Free_List.free_regs.size();

    //adjust free list head phase
    if(Free_List.head == 0){
        Free_List.h_phase = !Free_List.h_phase;
    }

    //return new physical register assignment from RMT
    //cerr << "successful rename: " << "reg: " << log_reg << " " << RMT[log_reg] << endl;//////////////////////////////////////////////////
    return RMT[log_reg];

    //cerr << "RN dest | ";

}


//Function to create new branch checkpoint
uint64_t renamer::checkpoint(){
    uint64_t tmp_gbm = GBM;
    uint64_t new_bit = 1;       //this will be used to modify GBM
    uint32_t position = 0;

    assert(!stall_branch(1));

    //scan through GBM checking for 0 bit
    for(uint32_t i = 0; i < Branch_Checkpoints.size(); i++){
        if((tmp_gbm & 1) == 0)    break;
        tmp_gbm = tmp_gbm >> 1;
        new_bit = new_bit << 1;
        position++;
    }
    assert(position < Branch_Checkpoints.size());

    GBM |= new_bit;         //adds 1 in correct in necessary bit position

    //add checkpoint information
    Branch_Checkpoints[position].RMT_shadow = RMT;
    //cerr << "Checkpoint success\n";
    Branch_Checkpoints[position].FL_head = Free_List.head;
    Branch_Checkpoints[position].FL_h_phase = Free_List.h_phase;
    Branch_Checkpoints[position].gbm_check = GBM;

    //cerr << "checkpoint | ";


    return position;
}

//Function to stall the dispatch stage
bool renamer::stall_dispatch(uint64_t bundle_inst){
    //temporary tail pointing to where it would be if bundle is added
    uint32_t occupancy;
    uint32_t size = Active_List.active_regs.size();

    //set occupancy value
    if(Active_List.h_phase == Active_List.t_phase){
        occupancy = Active_List.tail-Active_List.head;
    }
    else    occupancy = size - (Active_List.head - Active_List.tail);


    if((occupancy + bundle_inst) > size)    return true;

    return false;
}

//Function to dispatch a single instruction
uint64_t renamer::dispatch_inst(bool dest_valid, uint64_t log_reg, uint64_t phys_reg, bool load, bool store, bool branch, bool amo, bool csr, uint64_t PC){
    //ensure active list isn't full
    if(stall_dispatch(1)){
        cerr << Active_List.head << " | " << Active_List.tail;
    }
    assert(!stall_dispatch(1));


    uint32_t tmp_tail = Active_List.tail;
    //assign necessary variables
    Active_List.active_regs[tmp_tail].d_flag = dest_valid;
    Active_List.active_regs[tmp_tail].load_flag = load;
    Active_List.active_regs[tmp_tail].store_flag = store;
    Active_List.active_regs[tmp_tail].branch_flag = branch;
    Active_List.active_regs[tmp_tail].amo_flag = amo;
    Active_List.active_regs[tmp_tail].csr_flag = csr;
    Active_List.active_regs[tmp_tail].pc = PC;
        //safety assignment on problem flags
    Active_List.active_regs[tmp_tail].complete = false;
    Active_List.active_regs[tmp_tail].exception = false;
    Active_List.active_regs[tmp_tail].load_violation = false;
    Active_List.active_regs[tmp_tail].branch_misprediction = false;
    Active_List.active_regs[tmp_tail].set_value_misprediction = false;

        //conditional destination assignments
    if(dest_valid){
        Active_List.active_regs[tmp_tail].d_reg_logical = log_reg;
        Active_List.active_regs[tmp_tail].d_reg_physical = phys_reg;
    }

    
    //increment tail of active list
    Active_List.tail = (1 + Active_List.tail)  % Active_List.active_regs.size();

    //adjust tail phase
    if(Active_List.tail == 0)   Active_List.t_phase = !Active_List.t_phase;

    return tmp_tail;

}

//Function to indicate if physical register is ready
bool renamer::is_ready(uint64_t phys_reg){
    return PRF_ready[phys_reg];
}

//Function to clear ready bit of physical register
void renamer::clear_ready(uint64_t phys_reg){
    PRF_ready[phys_reg] = false;
}


//Function to return value from physical register
uint64_t renamer::read(uint64_t phys_reg){
    return PRF[phys_reg];
}

//Function to set ready bit of physical register
void renamer::set_ready(uint64_t phys_reg){
    PRF_ready[phys_reg] = true;
}

//Function to write value into physical register
void renamer::write(uint64_t  phys_reg, uint64_t value){
    PRF[phys_reg] = value;
}

//Function to set the completed bit of entry in active list
void renamer::set_complete(uint64_t AL_index){
    Active_List.active_regs[AL_index].complete = true;
}

//Function to handle branch resolution
void renamer::resolve(uint64_t AL_index, uint64_t branch_ID, bool correct){
    //safety checks
    assert(branch_ID < Branch_Checkpoints.size());
    assert(Branch_Checkpoints[branch_ID].RMT_shadow.size() > 0);

    uint64_t start = 1;
    uint64_t gbm_bit = start << branch_ID;
    //Branch Prediction Correct
    if(correct){
        //when checking if a branch relies on that branch ID, bitwise AND the GBM with gbm_bit, if result is gbm bit then that bit is set in the checkpoint
            //clear branch's bit in GBM
        GBM &= ~gbm_bit;
            //clear bit in checkpointed GBMs
        for(uint32_t i = 0; i < Branch_Checkpoints.size(); i++){
            //check if bit is set in that checkpoint
            if((Branch_Checkpoints[i].gbm_check & gbm_bit) == gbm_bit){
                Branch_Checkpoints[i].gbm_check &= ~gbm_bit;
            }
        }
        //cerr << "checkpoint removed(predicted)\n";
    }
    else{
        //Branch Prediction False
            //restore GBM from checkpoint(ensure that this branch's bit is set to 0)
            GBM = Branch_Checkpoints[branch_ID].gbm_check;
            GBM &= ~gbm_bit;
            //restore the RMT
            // for(uint32_t i = 0; i < RMT.size(); i++){
            //     RMT[i] = Branch_Checkpoints[branch_ID].RMT_shadow[i];
            // }
            RMT = Branch_Checkpoints[branch_ID].RMT_shadow;

            //restore the free list head and head phase
            Free_List.head = Branch_Checkpoints[branch_ID].FL_head;
            Free_List.h_phase = Branch_Checkpoints[branch_ID].FL_h_phase;
            
            //restore active list tail and tail phase(index after mispredicted branch)
            Active_List.tail = (AL_index + 1) % Active_List.active_regs.size();
            if(Active_List.tail > Active_List.head){
                Active_List.t_phase = Active_List.h_phase;
            }
            else    Active_List.t_phase = !Active_List.h_phase;

            //cerr << "Checkpoint removed(mispredicted)\n";
    }

    //cerr << "resolve | ";

}


//Function to examine instructions at the head of active list
bool renamer::precommit(bool &completed, 
    bool &exception, bool &load_viol, bool &br_misp, bool &val_misp, 
    bool &load, bool &store, bool &branch, bool &amo, bool &csr, 
    uint64_t &PC){

    //check if the active list is empty
    if((Active_List.head == Active_List.tail) && (Active_List.h_phase == Active_List.t_phase))  return false;

    //modify reference values
    completed = Active_List.active_regs[Active_List.head].complete;
    exception = Active_List.active_regs[Active_List.head].exception;
    load_viol = Active_List.active_regs[Active_List.head].load_violation;
    br_misp = Active_List.active_regs[Active_List.head].branch_misprediction;
    val_misp = Active_List.active_regs[Active_List.head].set_value_misprediction;
    load = Active_List.active_regs[Active_List.head].load_flag;
    store = Active_List.active_regs[Active_List.head].store_flag;
    branch = Active_List.active_regs[Active_List.head].branch_flag;
    amo = Active_List.active_regs[Active_List.head].amo_flag;
    csr = Active_List.active_regs[Active_List.head].csr_flag;
    PC = Active_List.active_regs[Active_List.head].pc;


    return true;
}

//Function to commit the instruction at the head of Active List
void renamer::commit(){
    //check for the following problem cases before committing
        //ensure active list not empty
    assert(!((Active_List.head == Active_List.tail) && (Active_List.h_phase == Active_List.t_phase)));
        //ensure head instruction is complete
    assert(Active_List.active_regs[Active_List.head].complete);
        //ensure head instruction is not an exception
    assert(!Active_List.active_regs[Active_List.head].exception);
        //ensure head instruction is not load violation
    assert(!Active_List.active_regs[Active_List.head].load_violation);

   

    //commit to AMT if there is destination register
    if(Active_List.active_regs[Active_List.head].d_flag){
        uint32_t tmp_log_reg = Active_List.active_regs[Active_List.head].d_reg_logical;

        //move physical register from AMT to Free List
        Free_List.free_regs[(Free_List.tail)] = AMT[tmp_log_reg];
        PRF_ready[AMT[tmp_log_reg]] = true;

        //increment tail and tail phase accordingly
        Free_List.tail = (Free_List.tail + 1) % Free_List.free_regs.size();
        if(Free_List.tail == 0)     Free_List.t_phase = !Free_List.t_phase;

        //move physical register from Active List to AMT
        AMT[tmp_log_reg] = Active_List.active_regs[Active_List.head].d_reg_physical;
    }


    //mark instruction as not complete(done to prevent errors later) 
    Active_List.active_regs[Active_List.head].complete = false;

    //increment head pointer and adjust phase if necessary
    Active_List.head = (1 + Active_List.head)  % Active_List.active_regs.size();
    if(Active_List.head == 0)       Active_List.h_phase = !Active_List.h_phase;

    //if(test_count > 31900  && test_count < 42000)      cerr << "Instructions retired: " << test_count;
    //cerr << "commit | ";

}

//Function to squash all instructions in the active list
void renamer::squash(){
    /*Fix the following structures
    GBM(set to 0)
    Free List(head = tail, phases are opposite)
    Active List(set tail to head, phases are the same)
    RMT(from AMT)
    */

    //GBM corrections
    GBM = 0;

    //Free List corrections
    Free_List.head = Free_List.tail;
    Free_List.h_phase = !Free_List.t_phase;

    //Active List corrections(important note: does not work when doing Active_List.tail = Active_List.head)
    Active_List.tail = Active_List.head;
    // Active_List.tail = 0;
    // Active_List.head = 0;
    Active_List.t_phase = Active_List.h_phase;



    //RMT Corrections
    for(uint32_t i = 0; i < RMT.size();i++){
        RMT[i] = AMT[i];
    }
    //cerr << "squash | ";
}

//Function to set exception bit
void renamer::set_exception(uint64_t AL_index){
    // test_count++;
    // cerr << test_count << endl;
    Active_List.active_regs[AL_index].exception = true;
}

//Function to set load violation bit
void renamer::set_load_violation(uint64_t AL_index){
    // test_count++;
    // cerr << test_count << endl;
    Active_List.active_regs[AL_index].load_violation = true;
}

//Function to set branch misprediction bit
void renamer::set_branch_misprediction(uint64_t AL_index){
    // test_count++;
    // cerr << test_count << endl;
    Active_List.active_regs[AL_index].branch_misprediction = true;
}

//Function to set value misprediction bit
void renamer::set_value_misprediction(uint64_t AL_index){
    // test_count++;
    // cerr << test_count << endl;
    Active_List.active_regs[AL_index].set_value_misprediction = true;
}

//Function to query the exception bit of entry
bool renamer::get_exception(uint64_t AL_index){
    return Active_List.active_regs[AL_index].exception;
}



