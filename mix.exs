defmodule Per.MixProject do
  use Mix.Project

  def project do
    [
      app: :per,
      version: "5.3.15",
      description: "The Per Programming Language",
      deps: deps(),
      package: package()
    ]
  end

  def application do
    [ extra_applications: [ :logger ] ]
  end

  def deps do
    [
      {:ex_doc, ">= 0.0.0", only: :dev}
    ]
  end

  def package() do
    [
      files: ["lib", "priv", "src", "test", "LICENSE", "README.md"],
      licenses: ["ISC"],
      maintainers: ["Namdak Tonpa"],
      name: :per,
      links: %{"GitHub" => "https://github.com/groupoid/per"}
    ]
  end

end
