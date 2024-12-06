from miasm.arch.x86.arch import mn_x86
from miasm.analysis.binary import Container
from miasm.analysis.machine import Machine
from miasm.core.locationdb import LocationDB
from future.utils import viewitems, viewvalues
from miasm.core.utils import encode_hex
from miasm.core.graph import DiGraph
from miasm.ir.ir import *
from miasm.expression.expression import *
from miasm.analysis.ssa import get_phi_sources_parent_block, \
    irblock_has_phi
from miasm.analysis.data_flow import ReachingDefinitions,\
    DiGraphDefUse

import logging

_log = logging.getLogger('modeflattener')

asmb = lambda patch_str, loc_db: mn_x86.asm(mn_x86.fromstring(patch_str, loc_db, 32))[0]
rel = lambda addr, patch_addr: hex(addr - patch_addr)


def save_cfg(cfg, name):
    import subprocess
    open(name, 'w').write(cfg.dot())
    subprocess.call(["dot", "-Tpng", name, "-o", name.split('.')[0]+'.png'])
    subprocess.call(["rm", name])


def print_disassembly(bytes):
    machine = Machine('x86_32')
    loc_db = LocationDB()
    c = Container.from_string(bytes, loc_db)
    mdis = machine.dis_engine(c.bin_stream, loc_db=loc_db)
    print(mdis.dis_multiblock(0))


def patch_gen(instrs, loc_db, nop_addrs, link):
    final_patch = b""
    start_addr = instrs[0].offset
    if instrs[-1].name.startswith('J'):
        instrs.pop()
    if instrs[-1].name.startswith('CMP'):
        instrs.pop()

    for instr in instrs:
        #omitting useless instructions
        if instr.offset not in nop_addrs:
            if instr.is_subcall():
                if isinstance(instr.args[0],ExprMem) or isinstance(instr.args[0],ExprId):
                    final_patch += instr.b
                else:
                    #generate asm for fixed calls with relative addrs
                    patch_addr = start_addr + len(final_patch)
                    tgt = loc_db.get_location_offset(instr.args[0].loc_key)
                    _log.info("CALL %#x" % tgt)
                    call_patch_str = "CALL %s" % rel(tgt, patch_addr)
                    _log.debug("call patch : %s" % call_patch_str)
                    call_patch = asmb(call_patch_str, loc_db)
                    final_patch += call_patch
                    _log.debug("call patch asmb : %s" % encode_hex(call_patch))
            else:
                #add the original bytes
                final_patch += instr.b

    patch_addr = start_addr + len(final_patch)
    _log.debug("jmps patch_addr : %#x", patch_addr)
    jmp_patches = b""
    # cleaning the control flow by patching with real jmps locs
    if 'cond' in link:
        t_addr = link['true_next']
        f_addr = link['false_next']
        jcc = link['cond'].replace('CMOV', 'J')
        _log.info("%s %#x" % (jcc, t_addr))
        _log.info("JMP %#x" % f_addr)

        patch1_str = "%s %s" % (jcc, rel(t_addr, patch_addr))
        jmp_patches += asmb(patch1_str, loc_db)
        patch_addr += len(jmp_patches)

        patch2_str = "JMP %s" % (rel(f_addr, patch_addr))
        jmp_patches += asmb(patch2_str, loc_db)
        _log.debug("jmp patches : %s; %s" % (patch1_str, patch2_str))

    else:
        n_addr = link['next']
        _log.info("JMP %#x" % n_addr)

        patch_str = "JMP %s" % rel(n_addr, patch_addr)
        jmp_patches = asmb(patch_str, loc_db)

        _log.debug("jmp patches : %s" % patch_str)

    _log.debug("jmp patches asmb : %s" % encode_hex(jmp_patches))
    final_patch += jmp_patches

    return final_patch


def get_cff_info(asmcfg):
    preds = {}
    for blk in asmcfg.blocks:
        offset = asmcfg.loc_db.get_location_offset(blk.loc_key)
        preds[offset] = asmcfg.predecessors(blk.loc_key)
    # pre-dispatcher is the one with max predecessors
    dispatcher = sorted(preds, key=lambda key: len(preds[key]), reverse=True)[0]
    # dispatcher is the one which suceeds pre-dispatcher
    pre_dispatcher = dispatcher

    # relevant blocks are those which preceed the pre-dispatcher
    relevant_blocks = []
    for loc in preds[pre_dispatcher]:
        offset = asmcfg.loc_db.get_location_offset(loc)
        relevant_blocks.append(offset)

    return relevant_blocks, dispatcher, pre_dispatcher


# do backwards search for jmp instruction to find start of relevant block
def get_block_father(asmcfg, blk_offset):
    blk = asmcfg.getby_offset(blk_offset)
    checklist = [blk.loc_key]

    pred = asmcfg.predecessors(blk.loc_key)[0]
    while True:
        curr_bloc = asmcfg.loc_key_to_block(pred)
        if curr_bloc.lines[-1].name in ['JZ', 'JMP', 'JNZ']:
            break
        checklist.append(pred)
        pred = asmcfg.predecessors(curr_bloc.loc_key)[0]

    return asmcfg.loc_db.get_location_offset(checklist[-1])


def get_phi_vars(ircfg,loc_db,mdis):
    res = []
    blks = list(ircfg.blocks)
    irblock = (ircfg.blocks[blks[-1]])
    parent_blks = None

    if irblock_has_phi(irblock):
        for dst, sources in viewitems(irblock[0]):
            phi_vars = sources.args
            parent_blks = get_phi_sources_parent_block(
                ircfg,
                irblock.loc_key,
                phi_vars
            )

    if not parent_blks:
        return []
    for var, loc in parent_blks.items():
        irblock = ircfg.get_block(list(loc)[0])
        for asg in irblock:
            dst, src = asg.items()[0]
            if dst == var and isinstance(src,ExprInt):
                res += [int(src)]
            elif dst==var and isinstance(src,ExprOp):
                reachings = ReachingDefinitions(ircfg)
                digraph = DiGraphDefUse(reachings)
                # the state var always a leaf
                for head in digraph.heads():
                    if head.var == src.args[0]:
                        head_offset=loc_db.get_location_offset(head.label)
                        if isinstance(mdis.dis_instr(head_offset).args[1],ExprInt):
                            res+=[int(mdis.dis_instr(head_offset).args[1])]

    return res


def _find_var_asg(ircfg, var):
    for lbl, irblock in viewitems(ircfg.blocks):
        for assignblk in irblock:
            found = False
            for exp in assignblk:
                if isinstance(exp, ExprId) and exp.name.startswith(var):
                    found = True
            if not found:
                continue
            yield assignblk


def find_var_asg(ircfg,var,loc_db,mdis):
    val_list = []
    res = {}
    # addr = loc_db.get_location_offset(ircfg.heads()[0])
    for assignblk in _find_var_asg(ircfg, var):
        dst, src = assignblk.items()[0]
        if isinstance(src, ExprInt):
            res['next'] = int(src)
            val_list += [int(src)]
        elif isinstance(src, ExprSlice):
            phi_vals = get_phi_vars(ircfg,loc_db,mdis)
            if not phi_vals:
                continue
            res['true_next'] = phi_vals[0]
            res['false_next'] = phi_vals[1]
            val_list += phi_vals
        elif isinstance(src,ExprId) or isinstance(src, ExprOp):
            phi_vals = get_phi_vars(ircfg,loc_db,mdis)
            if len(phi_vals) < 2:
                continue
            res['true_next'] = phi_vals[0]
            res['false_next'] = phi_vals[1]
            val_list += phi_vals
    return res, val_list


def get_assignment_parents(ircfg, label, index, reaching_defs):
    assignblk_reaching_defs = reaching_defs.get_definitions(label, index)
    assignblk = ircfg.get_block(label)[index]
    for lval, expr in viewitems(assignblk):
        read_vars = expr.get_r(mem_read=False)
        for read_var in read_vars:
            for reach in assignblk_reaching_defs.get(read_var, set()):
                label, index = reach
                return [assignblk] + get_assignment_parents(ircfg, label, index, reaching_defs)
    return [assignblk]


def find_state_var_usedefs(ircfg, search_var):
    var_addrs = set()
    reachings = ReachingDefinitions(ircfg)
    last_defs = list(reachings.items())[-1]
    for var, location in last_defs[1].items():
        label, index = next(iter(location))
        try:
            var.name
        except AttributeError:
            continue
        if var.name.startswith(search_var):
            for parent in get_assignment_parents(ircfg, label, index, reachings):
                var_addrs.add(parent.instr.offset)
    return var_addrs
