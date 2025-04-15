mod app;

fn main() {
    let app = app::common::create_app_helper();
    let fake_params = app::common::translate_args_for_iccma();
    app.launch_app_with_args(fake_params);
}
