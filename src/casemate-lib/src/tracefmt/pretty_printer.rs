use crate::shim::*;

use crate::transitions::*;

use crate::tracefmt::sexp::Sexp;

enum TransSexpField {
    Positional(String),
    WithKeyword(&'static str, String),
}

impl Into<Sexp> for TransSexpField {
    fn into(self) -> Sexp {
        match self {
            Self::Positional(s) => Sexp::value(s),
            Self::WithKeyword(kw, s) => Sexp::list(vec![kw.to_string(), s]),
        }
    }
}

struct TransSexpBuilder {
    name: Option<TransSexpField>,
    args: Vec<TransSexpField>,
    seq_id: Option<TransSexpField>,
    tid: Option<TransSexpField>,
    src_loc: Option<TransSexpField>,
}

impl TransSexpBuilder {
    fn new() -> Self {
        Self {
            name: None,
            args: vec![],
            seq_id: None,
            tid: None,
            src_loc: None,
        }
    }

    fn populate_metadata(&mut self, info: &TransitionInfo) {
        self.seq_id = Some(TransSexpField::WithKeyword(
            "seq_id",
            info.seq_id.to_string(),
        ));
        self.tid = Some(TransSexpField::WithKeyword("thread", info.tid.to_string()));
        self.src_loc = Some(TransSexpField::WithKeyword("src", info.src_loc.to_string()));
    }

    fn populate_name(&mut self, op: &Operation) {
        use Operation::*;
        let name = {
            match op {
                Write(_, _, _) => "write-mem",
                Read(_, _) => "read-mem",
                Barrier(_) => "barrier",
                TLBInval(_) => "tlbi",
                RegWrite(_, _) => "reg-write",
                RegRead(_, _) => "reg-read",
                InitMem(_, _) => "mem-init",
                MemSet {
                    loc: _,
                    size: _,
                    val: _,
                } => "mem-set",
                LockAcquire(_) => "lock",
                LockRelease(_) => "unlock",
                Hint(_) => "hint",
            }
        };
        self.name = Some(TransSexpField::Positional(name.to_string()));
    }

    fn populate_field<V>(&mut self, value: V)
    where
        V: ToString,
    {
        self.args
            .push(TransSexpField::Positional(value.to_string()));
    }

    fn populate_field_kw<V>(&mut self, key: &'static str, value: V)
    where
        V: ToString,
    {
        self.args
            .push(TransSexpField::WithKeyword(key, value.to_string()));
    }

    fn populate_address(&mut self, value: &PhysAddr) {
        self.populate_field_kw("address", value.0);
    }

    fn populate_value(&mut self, value: &u64) {
        self.populate_field_kw("value", value);
    }

    fn populate_barrier_kind(&mut self, kind: &BarrierKind) {
        use BarrierKind::*;
        self.populate_field(kind.clone());
        match kind {
            Arm_DMB(dxb) | Arm_DSB(dxb) => {
                self.populate_field_kw("kind", dxb);
            }
            Arm_ISB => (),
        }
    }

    fn populate_tlbi_kind(&mut self, kind: &TLBIKind) {
        use TLBIKind::*;
        self.populate_field(kind.clone());
        match kind {
            Arm_TLBI_vmalls12e1
            | Arm_TLBI_vmalls12e1is
            | Arm_TLBI_vmalle1is
            | Arm_TLBI_alle1is
            | Arm_TLBI_vmalle1 => (),
            Arm_TLBI_vale2is(r) | Arm_TLBI_vae2is(r) | Arm_TLBI_ipas2e1is(r) => {
                self.populate_value(r);
            }
        }
    }

    fn populate_location(&mut self, value: &PhysAddr) {
        self.populate_field_kw("location", value);
    }

    fn populate_hint_kind(&mut self, kind: &HintKind) {
        use HintKind::*;

        match kind {
            Set_Root_Lock { root, lock } => {
                self.populate_location(root);
                self.populate_value(&lock.0);
            }
            Associate_With_Root { loc, root } => {
                self.populate_location(loc);
                self.populate_value(&root.0);
            }
            Release_Tree { root } => {
                self.populate_location(root);
                self.populate_value(&0);
            }
            Set_Thread_Owner { loc, tid } => {
                self.populate_location(loc);
                self.populate_value(&(*tid).into());
            }
        }
    }

    fn populate_fields(&mut self, op: &Operation) {
        use Operation::*;
        match op {
            Write(a, mo, v) => {
                self.populate_address(a);
                self.populate_field_kw("mem-order", mo);
                self.populate_value(v);
            }
            Read(a, v) => {
                self.populate_address(a);
                self.populate_value(v);
            }
            Barrier(k) => {
                self.populate_barrier_kind(k);
            }
            TLBInval(tlbi_kind) => {
                self.populate_tlbi_kind(tlbi_kind);
            }
            RegWrite(name, value) => {
                self.populate_field_kw("sysreg", name);
                self.populate_value(value);
            }
            RegRead(_, _) => panic!("unsupported regread"),
            InitMem(a, s) => {
                self.populate_address(a);
                self.populate_field_kw("size", s);
            }
            MemSet { loc, size, val } => {
                self.populate_address(loc);
                self.populate_field_kw("size", size);
                self.populate_value(val);
            }
            LockAcquire(a) => {
                self.populate_address(a);
            }
            LockRelease(a) => {
                self.populate_address(a);
            }
            Hint(h) => {
                self.populate_field_kw("kind", h);
                self.populate_hint_kind(h);
            }
        }
    }

    fn from_trans(t: &Transition) -> Self {
        let mut builder = Self::new();
        builder.populate_name(&t.op);
        builder.populate_metadata(&t.info);
        builder.populate_fields(&t.op);
        builder
    }

    fn build(self) -> Sexp {
        let mut args: Vec<Sexp> = vec![];

        let push = &mut |f: TransSexpField| {
            args.push(f.into());
        };

        push(self.name.unwrap());
        push(self.seq_id.unwrap());
        push(self.tid.unwrap());

        for a in self.args {
            push(a);
        }

        push(self.src_loc.unwrap());
        Sexp::list(args)
    }
}

impl<'t> From<&Transition<'t>> for Sexp {
    fn from(t: &Transition) -> Self {
        let builder = TransSexpBuilder::from_trans(t);
        builder.build()
    }
}

pub fn emit_trace_sexpevent(t: &Transition) -> Sexp {
    Sexp::from(t)
}
