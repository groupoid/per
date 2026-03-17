defmodule Per.MixProject do
  use Mix.Project

  def project do
    [
      app: :per,
      version: "5.3.11",
      elixir: "~> 1.14",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  def application do
    [
      extra_applications: [:logger]
    ]
  end

  defp deps do
    []
  end
end
