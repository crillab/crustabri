mod app;

fn main() {
    let app = app::common::create_app_helper();
    let mut fake_params = app::common::translate_args_for_iccma();
    if fake_params.get(1) == Some(&"solve".to_string().into()) {
        if let Ok(path) = std::env::var("IPASIR_LIBRARY") {
            fake_params.push("--ipasir-library".to_string().into());
            fake_params.push(path.into());
        }
    }
    app.launch_app_with_args(fake_params);
}
