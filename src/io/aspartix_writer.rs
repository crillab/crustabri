use crate::aa::{AAFramework, Argument, LabelType};
use anyhow::{Context, Result};
use std::io::Write;

use super::ResponseWriter;

/// A writer for the Aspartix format.
///
/// This object is used to write an [`AAFramework`] using the Aspartix input format, as defined on [the Aspartix website](https://www.dbai.tuwien.ac.at/research/argumentation/aspartix/dung.html).
///
/// # Example
///
/// The following example retrieves an AF and writes it to the standard output using the Aspartix format.
///
/// ```
/// # use crustabri::aa::AAFramework;
/// # use crustabri::aa::ArgumentSet;
/// # use crustabri::io::AspartixWriter;
/// # use crustabri::aa::LabelType;
/// # use anyhow::Result;
/// fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
///     let writer = AspartixWriter::default();
///     writer.write_framework(&af, &mut std::io::stdout())
/// }
/// # write_af_to_stdout(&AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&[] as &[String])));
/// ```
#[derive(Default)]
pub struct AspartixWriter {}

impl AspartixWriter {
    /// Writes a framework using the Aspartix format to the provided writer.
    ///
    /// # Arguments
    ///
    /// * `framework` - the framework
    /// * `writer` - the writer
    ///
    /// # Example
    ///
    /// The following example retrieves an AF and writes it to the standard output using the Aspartix format.
    ///
    /// ```
    /// # use crustabri::aa::AAFramework;
    /// # use crustabri::aa::ArgumentSet;
    /// # use crustabri::io::AspartixWriter;
    /// # use crustabri::aa::LabelType;
    /// # use anyhow::Result;
    /// fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
    ///     let writer = AspartixWriter::default();
    ///     writer.write_framework(&af, &mut std::io::stdout())
    /// }
    /// # write_af_to_stdout(&AAFramework::new_with_argument_set(ArgumentSet::new_with_labels(&[] as &[String])));
    /// ```
    pub fn write_framework<T: LabelType>(
        &self,
        framework: &AAFramework<T>,
        writer: &mut dyn Write,
    ) -> Result<()> {
        let args = framework.argument_set();
        for arg in args.iter() {
            writeln!(writer, "arg({}).", arg)?;
        }
        for attack in framework.iter_attacks() {
            writeln!(writer, "att({},{}).", attack.attacker(), attack.attacked(),)?;
        }
        writer.flush()?;
        Ok(())
    }
}

impl ResponseWriter<String> for AspartixWriter {
    fn write_no_extension(&self, writer: &mut dyn Write) -> Result<()> {
        super::specs::write_no_extension(writer)
    }

    fn write_single_extension(
        &self,
        writer: &mut dyn Write,
        extension: &[&Argument<String>],
    ) -> Result<()> {
        let context = "while writing an extension";
        write!(writer, "[").context(context)?;
        let mut first = true;
        extension.iter().try_for_each(|arg| {
            if first {
                first = false;
                write!(writer, "{}", arg).context(context)
            } else {
                write!(writer, ",{}", arg).context(context)
            }
        })?;
        writeln!(writer, "]").context(context)?;
        writer.flush().context(context)
    }

    fn write_acceptance_status(
        &self,
        writer: &mut dyn Write,
        acceptance_status: bool,
    ) -> Result<()> {
        super::specs::write_acceptance_status(writer, acceptance_status)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aa::ArgumentSet;
    use std::io::BufWriter;

    #[test]
    fn test_write_af() {
        let arg_names = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_names);
        let mut framework = AAFramework::new_with_argument_set(args);
        framework.new_attack(&arg_names[0], &arg_names[0]).unwrap();
        framework.new_attack(&arg_names[1], &arg_names[2]).unwrap();
        let mut buffer = BufWriter::new(Vec::new());
        let writer = AspartixWriter::default();
        writer.write_framework(&framework, &mut buffer).unwrap();
        assert_eq!(
            "arg(a).\narg(b).\narg(c).\natt(a,a).\natt(b,c).\n",
            String::from_utf8(buffer.into_inner().unwrap()).unwrap()
        )
    }

    #[test]
    fn test_write_single_extension() {
        let arg_names = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let args = ArgumentSet::new_with_labels(&arg_names);
        let writer = AspartixWriter::default();
        let mut buffer = BufWriter::new(Vec::new());
        writer
            .write_single_extension(
                &mut buffer,
                &args.iter().collect::<Vec<&Argument<String>>>(),
            )
            .unwrap();
        assert_eq!(
            "[a,b,c]\n",
            String::from_utf8(buffer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_write_empty_extension() {
        let writer = AspartixWriter::default();
        let mut buffer = BufWriter::new(Vec::new());
        writer
            .write_single_extension(&mut buffer, &[] as &[&Argument<String>])
            .unwrap();
        assert_eq!(
            "[]\n",
            String::from_utf8(buffer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_write_no_extension() {
        let writer = AspartixWriter::default();
        let mut buffer = BufWriter::new(Vec::new());
        writer.write_no_extension(&mut buffer).unwrap();
        assert_eq!(
            "NO\n",
            String::from_utf8(buffer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_write_acceptance_status_yes() {
        let writer = AspartixWriter::default();
        let mut buffer = BufWriter::new(Vec::new());
        writer.write_acceptance_status(&mut buffer, true).unwrap();
        assert_eq!(
            "YES\n",
            String::from_utf8(buffer.into_inner().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_write_acceptance_status_no() {
        let writer = AspartixWriter::default();
        let mut buffer = BufWriter::new(Vec::new());
        writer.write_acceptance_status(&mut buffer, false).unwrap();
        assert_eq!(
            "NO\n",
            String::from_utf8(buffer.into_inner().unwrap()).unwrap()
        );
    }
}
