mod app;

fn main() {
    let app = app::common::create_app_helper();
    app.launch_app();
}
