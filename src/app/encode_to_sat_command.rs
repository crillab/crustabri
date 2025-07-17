use std::{cell::RefCell, fs, io::Read, rc::Rc};

use anyhow::Result;
use clap::{AppSettings, Arg, ArgMatches, SubCommand};
use scalop::{
    aa::Semantics,
    encodings::{
        aux_var_constraints_encoder, exp_constraints_encoder, ConstraintsEncoder,
        HybridCompleteConstraintsEncoder,
    },
    io::{AspartixReader, Iccma23Reader, InstanceReader},
    sat::{BufferedSatSolver, SatSolver, SatSolverFactory},
    solvers::{CompleteSemanticsSolver, SatEncoder, StableSemanticsSolver},
    utils::LabelType,
};

use crate::app::common::ARG_ENCODING;

use super::{cli_manager, command::Command, common};

const CMD_NAME: &str = "encode-to-sat";

const ARG_OUT: &str = "ARG_OUT";
const ARG_SEM: &str = "ARG_SEM";

pub(crate) struct EncodeToSatCommand;

impl EncodeToSatCommand {
    pub fn new() -> Self {
        EncodeToSatCommand
    }
}

impl<'a> Command<'a> for EncodeToSatCommand {
    fn name(&self) -> &str {
        CMD_NAME
    }

    fn clap_subcommand(&self) -> clap::App<'a, 'a> {
        SubCommand::with_name(CMD_NAME)
            .about("Solves an argumentation framework problem")
            .setting(AppSettings::DisableVersion)
            .arg(common::input_args())
            .arg(common::reader_arg())
            .arg(cli_manager::logging_level_cli_arg())
            .arg(common::encoding_arg())
            .arg(
                Arg::with_name(ARG_SEM)
                    .short("s")
                    .long("semantics")
                    .empty_values(false)
                    .multiple(false)
                    .possible_values(&["CO", "ST"])
                    .help("the semantics to encode")
                    .required(true),
            )
            .arg(
                Arg::with_name(ARG_OUT)
                    .short("o")
                    .long("output")
                    .empty_values(false)
                    .multiple(false)
                    .help("the output file for the encoding")
                    .required(false),
            )
    }

    fn execute(&self, arg_matches: &ArgMatches<'_>) -> Result<()> {
        match arg_matches.value_of(common::ARG_READER).unwrap() {
            "apx" => execute_with_reader(arg_matches, &mut AspartixReader::default()),
            "iccma23" => execute_with_reader(arg_matches, &mut Iccma23Reader::default()),
            _ => unreachable!(),
        }
    }
}

fn execute_with_reader<T>(
    arg_matches: &ArgMatches<'_>,
    reader: &mut dyn InstanceReader<T>,
) -> Result<()>
where
    T: LabelType,
{
    let file = arg_matches.value_of(common::ARG_INPUT).unwrap();
    let af = common::read_file_path(file, reader)?;
    let semantics = Semantics::try_from(arg_matches.value_of(ARG_SEM).unwrap()).unwrap();
    let instance = Rc::new(RefCell::new(Vec::new()));
    let fake_solver_factory = Box::new(FakeSatSolverFactory {
        instance: Rc::clone(&instance),
    });
    let mut sat_encoder: Box<dyn SatEncoder> = match semantics {
        Semantics::CO => {
            let str_encoding = arg_matches.value_of(ARG_ENCODING).unwrap_or("aux_var");
            let constraints_encoder: Box<dyn ConstraintsEncoder<T>> = match str_encoding {
                "aux_var" => Box::new(aux_var_constraints_encoder::new_for_complete_semantics()),
                "exp" => Box::new(exp_constraints_encoder::new_for_complete_semantics()),
                "hybrid" => Box::<HybridCompleteConstraintsEncoder>::default(),
                _ => unreachable!(),
            };
            Box::new(
                CompleteSemanticsSolver::new_with_sat_solver_factory_and_constraints_encoder(
                    &af,
                    fake_solver_factory,
                    constraints_encoder,
                ),
            )
        }
        Semantics::ST => Box::new(StableSemanticsSolver::new_with_sat_solver_factory(
            &af,
            fake_solver_factory,
        )),
        _ => unreachable!(),
    };
    let mut solver = sat_encoder.encode();
    solver.solve();
    let mut instance_content = Vec::new();
    std::mem::swap(&mut instance_content, &mut instance.borrow_mut());
    if let Some(output_file) = arg_matches.value_of(ARG_OUT) {
        fs::write(output_file, String::from_utf8(instance_content).unwrap())?;
    } else {
        println!("{}", String::from_utf8(instance_content).unwrap());
    }
    Ok(())
}

struct FakeSatSolverFactory {
    instance: Rc<RefCell<Vec<u8>>>,
}

impl SatSolverFactory for FakeSatSolverFactory {
    fn new_solver(&self) -> Box<dyn SatSolver> {
        Box::new(BufferedSatSolver::new(Box::new({
            let instance_cl = Rc::clone(&self.instance);
            move |mut r| {
                r.read_to_end(&mut instance_cl.borrow_mut()).unwrap();
                Box::new("s UNSATISFIABLE".as_bytes())
            }
        })))
    }
}
